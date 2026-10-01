/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FirstRamificationPGroup
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Wild inertia as an inverse limit of finite p-groups

Finite-coordinate kernels control continuous discrete images. Compactness of
inertia realizes every compatible family of finite first-ramification elements.
-/

@[expose] public section

open NumberField IsLocalRing
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

/-- The coordinate of wild inertia in a finite first group. -/
noncomputable def wildFiniteRestriction (N : OpenNormalSubgroup Γ) :
    wildInertia v →* firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv) :=
  ((finiteRestriction v N).comp (wildInertia v).subtype).codRestrict _ fun σ ↦
    (mem_wildInertia_iff v σ.1).mp σ.2 N

/-- The kernel of an absolute finite-level restriction is the given open normal subgroup. -/
theorem finiteRestriction_eq_one_iff (N : OpenNormalSubgroup Γ) (σ : localInertiaGroup v) :
    finiteRestriction v N σ = 1 ↔ σ.1 ∈ N := by
  change σ.1 ∈ (AlgEquiv.restrictNormalHom (IntermediateField.fixedField N.1.1)).ker ↔ _
  rw [IntermediateField.restrictNormalHom_ker,
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup Γ)]
  rfl

/-- Every continuous homomorphism to a discrete group kills a finite-coordinate kernel. -/
theorem exists_wildFiniteRestriction_ker_le (H : Type*) [Group H]
    [TopologicalSpace H] [DiscreteTopology H]
    (f : wildInertia v →* H) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup Γ, (wildFiniteRestriction v N).ker ≤ f.ker := by
  have hopen : IsOpen (f.ker : Set (wildInertia v)) :=
    hf.isOpen_preimage _ (isOpen_discrete {1})
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hU
  have h1 : (1 : Γ) ∈ V := by
    have h : (1 : wildInertia v) ∈ (f.ker : Set _) := f.ker.one_mem
    rw [← hUeq, ← hVeq] at h
    exact h
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨N, fun σ hσ ↦ ?_⟩
  rw [← SetLike.mem_coe, ← hUeq, ← hVeq]
  apply hN
  apply (finiteRestriction_eq_one_iff v N σ.1).mp
  exact congrArg Subtype.val (show wildFiniteRestriction v N σ = 1 from hσ)

/-- Every continuous finite image of wild inertia is a p-group.
The finite target binder retains the standard pro-p endpoint interface. -/
@[nolint unusedArguments]
theorem wildInertia_finite_image_isPGroup
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    (H : Type*) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : wildInertia v →* H) (hf : Continuous f) : IsPGroup p f.range := by
  obtain ⟨N, hN⟩ := exists_wildFiniteRestriction_ker_le v H f hf
  intro y
  obtain ⟨σ, hσ⟩ := y.2
  obtain ⟨n, hn⟩ := finite_firstGroup_isPGroup v p N (wildFiniteRestriction v N σ)
  refine ⟨n, Subtype.ext ?_⟩
  change y.1 ^ p ^ n = 1
  rw [← hσ, ← map_pow]
  apply hN
  change wildFiniteRestriction v N (σ ^ p ^ n) = 1
  rwa [map_pow]

/-- The finite fixed fields carry their canonical finite-dimensional structure. -/
local instance finiteLevelFiniteDimensional (N : OpenNormalSubgroup Γ) :
    FiniteDimensional Kv (IntermediateField.fixedField N.1.1) := by
  rw [← InfiniteGalois.isOpen_iff_finite,
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup Γ)]
  exact N.isOpen'

/-- Finite restriction is continuous for the Krull topologies. -/
theorem finiteRestriction_continuous (N : OpenNormalSubgroup Γ) :
    Continuous (finiteRestriction v N) :=
  (InfiniteGalois.restrictNormalHom_continuous _).comp continuous_subtype_val

/-- A finite first-group element lifts to absolute inertia. -/
theorem exists_inertia_lift_first (N : OpenNormalSubgroup Γ)
    (σ : firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv)) :
    ∃ τ : localInertiaGroup v, finiteRestriction v N τ = σ.1 := by
  have h := firstGroup_le_inertia _ _ σ.2
  rw [← map_localInertiaGroup_eq_finiteInertia v N] at h
  obtain ⟨τ, hτ, heq⟩ := h
  exact ⟨⟨τ, hτ⟩, heq⟩

/-- Identity law for the finite first-group transition maps. -/
theorem finiteFirstTowerRestriction_refl (N : OpenNormalSubgroup Γ) :
    finiteFirstTowerRestriction v (le_refl N) = MonoidHom.id _ := by
  ext σ : 1
  apply Subtype.ext
  obtain ⟨τ, hτ⟩ := exists_inertia_lift_first v N σ
  change finiteTowerRestriction v (le_refl N) σ.1 = σ.1
  rw [← hτ]
  exact DFunLike.congr_fun (finiteTowerRestriction_comp v (le_refl N)) τ

/-- Composition law for the finite first-group transition maps. -/
theorem finiteFirstTowerRestriction_trans {N M L : OpenNormalSubgroup Γ}
    (hNM : N ≤ M) (hML : M ≤ L) :
    (finiteFirstTowerRestriction v hML).comp (finiteFirstTowerRestriction v hNM) =
      finiteFirstTowerRestriction v (hNM.trans hML) := by
  ext σ : 1
  apply Subtype.ext
  obtain ⟨τ, hτ⟩ := exists_inertia_lift_first v N σ
  change finiteTowerRestriction v hML (finiteTowerRestriction v hNM σ.1) =
    finiteTowerRestriction v (hNM.trans hML) σ.1
  rw [← hτ]
  have h₁ := DFunLike.congr_fun (finiteTowerRestriction_comp v hNM) τ
  have h₂ := DFunLike.congr_fun (finiteTowerRestriction_comp v hML) τ
  have h₃ := DFunLike.congr_fun (finiteTowerRestriction_comp v (hNM.trans hML)) τ
  exact (congrArg (finiteTowerRestriction v hML) h₁).trans (h₂.trans h₃.symm)

/-- Wild inertia is closed in inertia. -/
theorem wildInertia_isClosed : IsClosed (wildInertia v : Set (localInertiaGroup v)) := by
  rw [wildInertia, Subgroup.coe_iInf]
  refine isClosed_iInter fun N ↦ ?_
  rw [Subgroup.coe_comap]
  exact (isClosed_discrete _).preimage (finiteRestriction_continuous v N)

/-- Wild inertia has its compact subgroup topology. -/
instance wildInertiaCompactSpace : CompactSpace (wildInertia v) := by
  let : CompactSpace (localInertiaGroup v) :=
    isCompact_iff_compactSpace.mp (localInertiaGroup_isClosed v).isCompact
  exact isCompact_iff_compactSpace.mp (wildInertia_isClosed v).isCompact

/-- Compatible families of finite first groups, with restrictions computed in the
ambient finite Galois groups. The topology is inherited from their product. -/
def compatibleFirstGroups : Subgroup (∀ N : OpenNormalSubgroup Γ,
    firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv)) where
  carrier := {g | ∀ (N M) (h : N ≤ M), finiteTowerRestriction v h (g N).1 = (g M).1}
  one_mem' := by intro N M h; exact map_one _
  mul_mem' := by intro a b ha hb N M h; simp only [Pi.mul_apply, Subgroup.coe_mul,
    map_mul, ha N M h, hb N M h]
  inv_mem' := by intro a ha N M h; simp only [Pi.inv_apply, Subgroup.coe_inv, map_inv, ha N M h]

/-- Compatibility can equivalently be written with the first-group transition maps. -/
theorem mem_compatibleFirstGroups_iff (g : ∀ N : OpenNormalSubgroup Γ,
    firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv)) :
    g ∈ compatibleFirstGroups v ↔ ∀ N M h, finiteFirstTowerRestriction v h (g N) = g M := by
  constructor
  · intro hg N M h
    exact Subtype.ext (hg N M h)
  · intro hg N M h
    exact congrArg Subtype.val (hg N M h)

/-- Send wild inertia to its family of finite coordinates. -/
noncomputable def wildInertiaToCompatible : wildInertia v →* compatibleFirstGroups v :=
  (MonoidHom.pi (wildFiniteRestriction v)).codRestrict _ fun σ _N _M h ↦
    DFunLike.congr_fun (finiteTowerRestriction_comp v h) σ.1

/-- Finite coordinates separate wild-inertia elements. -/
theorem wildInertiaToCompatible_injective : Function.Injective (wildInertiaToCompatible v) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply Subtype.ext
  by_contra h
  have h1 : (1 : Γ) ∈ ({σ.1.1} : Set Γ)ᶜ := by simpa using Ne.symm h
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    isClosed_singleton.isOpen_compl h1
  have hcoord : finiteRestriction v N σ.1 = 1 :=
    congrArg (fun g : compatibleFirstGroups v ↦ (g.1 N).1) hσ
  exact hN ((finiteRestriction_eq_one_iff v N σ.1).mp hcoord) rfl

/-- The coordinate map is continuous into the product subspace. -/
theorem wildInertiaToCompatible_continuous : Continuous (wildInertiaToCompatible v) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro N
  exact ((finiteRestriction_continuous v N).comp continuous_subtype_val).subtype_mk _

set_option maxHeartbeats 1000000 in
-- Nested finite Galois restriction types need additional elaboration time.
/-- Every compatible family is realized by wild inertia, using compactness of inertia. -/
theorem wildInertiaToCompatible_surjective : Function.Surjective (wildInertiaToCompatible v) := by
  intro g
  let : Nonempty (OpenNormalSubgroup Γ) := ⟨⟨⊤, by change (⊤ : Subgroup Γ).Normal; infer_instance⟩⟩
  let : CompactSpace (localInertiaGroup v) :=
    isCompact_iff_compactSpace.mp (localInertiaGroup_isClosed v).isCompact
  let C (N : OpenNormalSubgroup Γ) : Set (localInertiaGroup v) :=
    {σ | finiteRestriction v N σ = (g.1 N).1}
  have hc (N) : IsClosed (C N) :=
    isClosed_eq (finiteRestriction_continuous v N) continuous_const
  have hn (N) : (C N).Nonempty := exists_inertia_lift_first v N (g.1 N)
  have hsub {N M : OpenNormalSubgroup Γ} (h : N ≤ M) : C N ⊆ C M := by
    intro σ hσ
    exact (DFunLike.congr_fun (finiteTowerRestriction_comp v h) σ).symm.trans
      ((congrArg (finiteTowerRestriction v h) hσ).trans (g.2 N M h))
  have hd : Directed (· ⊇ ·) C := fun N M ↦
    ⟨N ⊓ M, hsub inf_le_left, hsub inf_le_right⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hd hn (fun N ↦ (hc N).isCompact) hc
  have hs (N) : finiteRestriction v N σ = (g.1 N).1 := Set.mem_iInter.mp hσ N
  have hw : σ ∈ wildInertia v := (mem_wildInertia_iff v σ).mpr fun N ↦ by
    rw [hs N]
    exact (g.1 N).2
  refine ⟨⟨σ, hw⟩, Subtype.ext ?_⟩
  funext N
  exact Subtype.ext (hs N)

/-- Wild inertia is the topological group of compatible finite first-ramification elements. -/
noncomputable def wildInertiaEquivCompatible : wildInertia v ≃ₜ* compatibleFirstGroups v := by
  let e := MulEquiv.ofBijective (wildInertiaToCompatible v)
    ⟨wildInertiaToCompatible_injective v, wildInertiaToCompatible_surjective v⟩
  have he : Continuous e.toEquiv := wildInertiaToCompatible_continuous v
  exact { e with
    continuous_toFun := wildInertiaToCompatible_continuous v
    continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

/-- The comparison sends each element to its original finite restriction. -/
@[simp] theorem wildInertiaEquivCompatible_apply (σ : wildInertia v)
    (N : OpenNormalSubgroup Γ) :
    (wildInertiaEquivCompatible v σ).1 N = wildFiniteRestriction v N σ := rfl

end LocalRamification
