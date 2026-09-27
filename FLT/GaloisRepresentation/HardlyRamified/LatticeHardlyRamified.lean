/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CoefficientQuotient
public import FLT.GaloisRepresentation.HardlyRamified.FlatCoefficientExtension
public import FLT.GaloisRepresentation.HardlyRamified.NormalizedOrder
public import FLT.Slop.Ribet_Lemma.LatticeFlat
public import FLT.Slop.Ribet_Lemma.LatticeTameTwo
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Hardly ramified representations on stable lattices

Hardly ramified representations remain hardly ramified on any stable lattice
in their normalized generic fibre, and on the residue representations.
-/

@[expose] public section

open Module IsLocalRing GaloisRepresentation TensorProduct
open scoped TensorProduct NumberField ThreeAdicPlan

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

/-- Flatness is invariant under an equivariant change of coordinates. -/
theorem flatAt_conj {R V W : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
    (ρ : GaloisRep ℚ R V) (e : V ≃ₗ[R] W)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (hρ : ρ.IsFlatAt v) :
    (ρ.conj e).IsFlatAt v := by
  constructor
  intro I hI
  let σ := (ρ.baseChange (R ⧸ I)).toLocal v
  let τ := ((ρ.conj e).baseChange (R ⧸ I)).toLocal v
  let eI := e.baseChange R (R ⧸ I) V W
  let f : σ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] τ.Space :=
    { eI.toAddMonoidHom with
      map_smul' := by
        intro g x
        change eI (σ g x) = τ g (eI x)
        induction x using TensorProduct.inductionOn with
        | tmul r x =>
          change r ⊗ₜ[R] e (ρ.toLocal v g x) = r ⊗ₜ[R] e (ρ.toLocal v g (e.symm (e x)))
          rw [e.symm_apply_apply]
        | add x y hx hy => simp_all }
  exact (hρ.cond I hI).map _ _ _ _ f eI.bijective

/-- Hardly ramified is invariant under a change of coordinates. -/
theorem hardlyRamified_conj {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {R V W : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
    (hV : Module.rank R V = 2) (hW : Module.rank R W = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hp hV ρ) (e : V ≃ₗ[R] W) :
    IsHardlyRamified hp hW (ρ.conj e) := by
  refine ⟨?_, ?_, flatAt_conj ρ e _ hρ.isFlat, ?_⟩
  · intro g
    change (e.conj (ρ g)).det = _
    exact (LinearMap.det_conj (ρ g) e).trans (hρ.det g)
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    infer_instance
  · obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
    refine ⟨π.comp e.symm.toLinearMap, hπ.comp e.symm.surjective, δ, ?_⟩
    intro g x
    simpa [GaloisRep.map_conj, GaloisRep.conj_apply_apply] using hδ g (e.symm x)

/-- Coefficient extension preserves the other three clauses whenever flatness is known. -/
@[nolint unusedArguments]
theorem hardlyRamified_baseChange_of_flat {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R A : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra ℤ_[p] A] [Algebra R A] [IsScalarTower ℤ_[p] R A]
    [ContinuousSMul R A]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (hVA : Module.rank A (A ⊗[R] V) = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ)
    (hflat : (ρ.baseChange A).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))) :
    IsHardlyRamified hpodd hVA (ρ.baseChange A) := by
  refine ⟨?_, ?_, hflat, ?_⟩
  · intro g
    change ((ρ g).baseChange A).det = _
    rw [LinearMap.det_baseChange]
    change algebraMap R A (ρ.det g) = _
    rw [hρ.det, ← IsScalarTower.algebraMap_apply ℤ_[p] R A]
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    infer_instance
  · obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
    let e : A ⊗[R] R ≃ₗ[A] A := AlgebraTensorModule.rid R A A
    let πA : A ⊗[R] V →ₗ[A] A := e.toLinearMap.comp (π.baseChange A)
    let δA := (δ.baseChange A).conj e
    have hker : δ.ker ≤ δA.ker := by
      dsimp [δA]
      rw [GaloisRep.ker_conj]
      exact δ.ker_baseChange
    refine ⟨πA, e.surjective.comp (π.baseChange_surjective A hπ), δA, ?_⟩
    intro g x
    refine ⟨?_, (hδ 1 0).2.1.trans hker, ?_⟩
    · induction x using TensorProduct.inductionOn with
      | tmul a v =>
        have hv := (hδ g v).1
        have hδlin : δ g (π v) = π v • δ g 1 := by
          simpa using (δ g).map_smul (π v) (1 : R)
        simp only [GaloisRep.baseChange_map, GaloisRep.baseChange_tmul,
          πA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
          e, AlgebraTensorModule.rid_tmul, δA, GaloisRep.conj_apply_apply,
          AlgebraTensorModule.rid_symm_apply]
        rw [hv, hδlin]
        simp [smul_smul, mul_comm]
      | add x y hx hy => simp_all
    · intro g
      have hgg : g * g ∈ δ.ker := by
        change δ (g * g) = 1
        rw [map_mul, (hδ 1 0).2.2 g]
      have hggA := hker hgg
      change δA (g * g) = 1 at hggA
      rwa [map_mul] at hggA


section Lattices

variable {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- The lattice determinant maps to the generic-fibre determinant. -/
theorem lattice_det (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (g : Field.absoluteGaloisGroup ℚ) :
    let := hΛ.isLattice
    algebraMap O K ((latticeGaloisRep ρK Λ hΛ hOK).det g) = (ρK g).det := by
  let := hΛ.isLattice
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
  obtain ⟨e, he⟩ := lattice_generic_equiv ρK Λ hΛ hOK
  have h := congrArg (fun σ : GaloisRep ℚ K W ↦ (σ g).det) he
  exact (LinearMap.det_baseChange (latticeGaloisRep ρK Λ hΛ hOK g) (A := K)).symm.trans
    ((LinearMap.det_conj ((latticeGaloisRep ρK Λ hΛ hOK g).baseChange K) e).symm.trans h)

/-- Inertia acting trivially on the generic fibre acts trivially on a lattice. -/
theorem lattice_unramified (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (hρ : ρK.IsUnramifiedAt v) :
    (latticeGaloisRep ρK Λ hΛ hOK).IsUnramifiedAt v := by
  constructor
  intro g hg
  have hgK := hρ.localInertiaGroup_le hg
  change ρK.toLocal v g = 1 at hgK
  change (latticeGaloisRep ρK Λ hΛ hOK).toLocal v g = 1
  ext x
  change ρK.toLocal v g (x : W) = x
  rw [hgK]
  rfl

/-- All four hardly-ramified clauses are independent of the stable lattice. -/
theorem hardlyRamified_lattice_transfer {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [Algebra ℤ_[p] O] (ρK : GaloisRep ℚ K W) (Λ₀ Λ : Submodule O W)
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (h₀dim : Module.rank O Λ₀ = 2) (hΛdim : Module.rank O Λ = 2)
    (hρ : let := h₀.isLattice
      IsHardlyRamified hp h₀dim (latticeGaloisRep ρK Λ₀ h₀ hOK)) :
    let := hΛ.isLattice
    IsHardlyRamified hp hΛdim (latticeGaloisRep ρK Λ hΛ hOK) := by
  let := h₀.isLattice
  let := hΛ.isLattice
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
  refine ⟨?_, ?_, flat_three_of_stable_lattice ρK Λ₀ Λ h₀ hΛ hOK _ hρ.isFlat,
    tame_two_of_stable_lattice ρK Λ₀ Λ h₀ hΛ hOK hρ.isTameAtTwo⟩
  · intro g
    apply IsFractionRing.injective O K
    rw [lattice_det, ← lattice_det ρK Λ₀ h₀ hOK, hρ.det]
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    obtain ⟨e, he⟩ := lattice_generic_equiv ρK Λ₀ h₀ hOK
    have hK : ρK.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
      rw [← he]
      infer_instance
    exact lattice_unramified ρK Λ hΛ hOK _ hK

/-- A hardly-ramified residue representation together with its identification
with the algebraic lattice reduction. -/
abbrev HardlyRamifiedReduction {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [Algebra ℤ_[p] O]
    [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
    [ContinuousSMul O (ResidueField O)]
    (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) : Prop :=
    let := hΛ.isLattice
    ∃ (hdim : Module.rank (ResidueField O) (ResidueField O ⊗[O] Λ) = 2)
      (e : (ResidueField O ⊗[O] Λ) ≃ₗ[ResidueField O] StableLattice.Reduction O W Λ),
      IsHardlyRamified hp hdim ((latticeGaloisRep ρK Λ hΛ hOK).baseChange (ResidueField O)) ∧
      ∀ g x, e (((latticeGaloisRep ρK Λ hΛ hOK).baseChange (ResidueField O)) g x) =
        StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g (e x)

/-- Residue coefficient extension preserves hardly-ramified stable lattices.
The resulting continuous representation identifies with the algebraic reduction. -/
theorem hardlyRamified_lattice_reduction {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [Algebra ℤ_[p] O]
    [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
    [ContinuousSMul O (ResidueField O)]
    (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hΛdim : Module.rank O Λ = 2)
    (hρ : let := hΛ.isLattice
      IsHardlyRamified hp hΛdim (latticeGaloisRep ρK Λ hΛ hOK)) :
    HardlyRamifiedReduction hp ρK Λ hΛ hOK := by
  let := hΛ.isLattice
  have hdim : Module.rank (ResidueField O) (ResidueField O ⊗[O] Λ) = 2 := by
    simpa [Module.rank_baseChange] using hΛdim
  obtain ⟨e, he⟩ := lattice_residue_equiv ρK Λ hΛ hOK
  refine ⟨hdim, e, ?_, he⟩
  exact B5Inputs.hardlyRamified_of_surjective_coefficients hp
    (R := O) (A := ResidueField O) (ρ := latticeGaloisRep ρK Λ hΛ hOK)
    (IsLocalRing.residue_surjective (R := O)) hΛdim hdim hρ

end Lattices

/-- The image of an integral representation in its generic fibre is a stable
lattice, canonically isomorphic to the integral representation. -/
theorem exists_initial_stable_lattice
    {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousSMul O K]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [Module.Free O V]
    (ρ : GaloisRep ℚ O V) (hOK : Topology.IsInducing (algebraMap O K)) :
    ∃ (Λ : Submodule O (K ⊗[O] V))
      (hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ)
      (e : V ≃ₗ[O] Λ), ρ.conj e = latticeGaloisRep (ρ.baseChange K) Λ hΛ hOK := by
  classical
  let j : V →ₗ[O] K ⊗[O] V := TensorProduct.mk O K V 1
  let Λ := LinearMap.range j
  have hj : Function.Injective j := Module.Flat.tensorProduct_mk_injective O V K
  have hlat : Submodule.IsLattice K Λ := by
    constructor
    · simpa only [Submodule.map_top] using Module.Finite.fg_top.map j
    · apply top_unique
      intro x hx
      clear hx
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        have hx : j x ∈ Submodule.span K (Λ : Set (K ⊗[O] V)) :=
          Submodule.subset_span (LinearMap.mem_range_self j x)
        have hs := (Submodule.span K (Λ : Set (K ⊗[O] V))).smul_mem a hx
        change a • ((1 : K) ⊗ₜ[O] x) ∈ _ at hs
        simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hs
      | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hstable : StableLattice.Stabilizes (ρ.baseChange K).toRepresentation Λ := by
    intro g
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨ρ g z, rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨j (ρ g⁻¹ z), LinearMap.mem_range_self j _, ?_⟩
      change (1 : K) ⊗ₜ[O] (ρ g (ρ g⁻¹ z)) = (1 : K) ⊗ₜ[O] z
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  let hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ :=
    ⟨hlat, hstable⟩
  let e : V ≃ₗ[O] Λ := LinearEquiv.ofInjective j hj
  refine ⟨Λ, hΛ, e, ?_⟩
  ext g x
  change j (ρ g (e.symm x)) = (ρ.baseChange K) g (x : K ⊗[O] V)
  have hx : j (e.symm x) = (x : K ⊗[O] V) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [← hx]
  rfl

/-- An integral hardly-ramified model gives hardly-ramified representations on
all stable lattices of its generic fibre. -/
theorem hardlyRamified_of_integral_lattice {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Field K] [Algebra O K] [IsFractionRing O K]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousSMul O K]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [Module.Free O V]
    (hV : Module.rank O V = 2) {ρ : GaloisRep ℚ O V}
    (hρ : IsHardlyRamified hp hV ρ)
    (Λ : Submodule O (K ⊗[O] V))
    (hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hΛdim : Module.rank O Λ = 2) :
    let := hΛ.isLattice
    IsHardlyRamified hp hΛdim (latticeGaloisRep (ρ.baseChange K) Λ hΛ hOK) := by
  obtain ⟨Λ₀, h₀, e, he⟩ := exists_initial_stable_lattice ρ hOK
  let := h₀.isLattice
  have h₀dim : Module.rank O Λ₀ = 2 := e.rank_eq.symm.trans hV
  have h₀HR := hardlyRamified_conj hp hV h₀dim hρ e
  rw [he] at h₀HR
  exact hardlyRamified_lattice_transfer hp (ρ.baseChange K) Λ₀ Λ h₀ hΛ hOK
    h₀dim hΛdim h₀HR

section Normalization

variable {R V : Type} [CommRing R] [IsLocalRing R] [IsDomain R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

/-- Prefer the spectral-norm topology of L0-N to the generic localization
topology that is also available after importing the representation lemmas. -/
scoped instance (priority := 1100) normalizedFractionTopology :
    TopologicalSpace (FractionRing R) :=
  (fractionNormedField R).toUniformSpace.toTopologicalSpace

/-- The normalization's residue field has the quotient topology. -/
scoped instance normalizedResidueTopology : TopologicalSpace (ResidueField (NormalizedOrder R)) :=
  inferInstanceAs (TopologicalSpace (NormalizedOrder R ⧸ maximalIdeal (NormalizedOrder R)))

scoped instance normalizedResidueTopologicalRing :
    IsTopologicalRing (ResidueField (NormalizedOrder R)) :=
  inferInstanceAs (IsTopologicalRing (NormalizedOrder R ⧸ maximalIdeal (NormalizedOrder R)))

set_option synthInstance.maxHeartbeats 100000 in
-- The nested normalization and tensor scalar instances require additional synthesis.
scoped instance normalizedResidueContinuousSMul :
    ContinuousSMul (NormalizedOrder R) (ResidueField (NormalizedOrder R)) :=
  inferInstanceAs (ContinuousSMul (NormalizedOrder R)
    (NormalizedOrder R ⧸ maximalIdeal (NormalizedOrder R)))

omit [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsModuleTopology ℤ_[3] R] in
/-- Every open ideal of the normalization contains a power of three and has
finite quotient, as needed by coefficient-extension flatness. -/
@[nolint unusedArguments]
theorem normalizedOrder_open_ideal (J : Ideal (NormalizedOrder R))
    (hJ : IsOpen (J : Set (NormalizedOrder R))) :
    ∃ n : ℕ, (3 : NormalizedOrder R) ^ n ∈ J ∧ Finite (NormalizedOrder R ⧸ J) := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (3 : ℤ_[3]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      change ‖((3 : ℕ) : ℤ_[3])‖ < 1
      rw [PadicInt.norm_p]; norm_num)
  have hc : Filter.Tendsto (fun n : ℕ ↦ (3 : NormalizedOrder R) ^ n)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, map_pow, map_ofNat, map_zero] using
      (continuous_algebraMap ℤ_[3] (NormalizedOrder R)).tendsto 0 |>.comp ht
  have he : ∀ᶠ n : ℕ in Filter.atTop, (3 : NormalizedOrder R) ^ n ∈ J :=
    hc (hJ.mem_nhds J.zero_mem)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn, IsLocalRing.isOpen_iff_finite_quotient.mp hJ⟩

/-- Normalizing the coefficient order preserves all four hardly-ramified clauses. -/
theorem hardlyRamified_normalization (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ) :
    IsHardlyRamified (by decide : Odd 3)
      (show Module.rank (NormalizedOrder R) (NormalizedOrder R ⊗[R] V) = 2 by
        simpa [Module.rank_baseChange] using hV)
      (ρ.baseChange (NormalizedOrder R)) := by
  let : Module.Finite R (NormalizedOrder R) := Module.Finite.of_restrictScalars_finite ℤ_[3] R _
  exact hardlyRamified_baseChange_of_flat (p := 3) (R := R) (A := NormalizedOrder R)
    (by decide) hV _ hρ
    (flat_three_normalization (p := 3) (R := R) (O := NormalizedOrder R)
      normalizedOrder_open_ideal ρ _ hρ.isFlat)

omit [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R] in
/-- The normalized residue field carries the discrete quotient topology. -/
@[nolint unusedArguments]
theorem normalizedOrder_residue_discrete :
    DiscreteTopology (ResidueField (NormalizedOrder R)) :=
  QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal (NormalizedOrder R))

omit [IsTopologicalRing R] in
/-- The iterated normalized generic fibre is the ordinary generic fibre,
via the canonical tensor cancellation equivalence. -/
theorem normalized_generic_equiv (ρ : GaloisRep ℚ R V) :
    ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R)).conj
      (AlgebraTensorModule.cancelBaseChange R (NormalizedOrder R) (FractionRing R)
        (FractionRing R) V) = ρ.baseChange (FractionRing R) := by
  let := moduleTopology (FractionRing R)
    (Module.End (FractionRing R) (FractionRing R ⊗[R] V))
  apply ContinuousMonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  let e := AlgebraTensorModule.cancelBaseChange R (NormalizedOrder R) (FractionRing R)
    (FractionRing R) V
  change e (((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R)) g
    (e.symm x)) = (ρ.baseChange (FractionRing R)) g x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [e, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      GaloisRep.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp_all

set_option synthInstance.maxHeartbeats 100000 in
-- The nested normalization and tensor scalar instances require additional synthesis.
omit [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [Module.Finite R V] in
/-- Every normalized generic-fibre lattice has the rank of the original model. -/
theorem normalized_lattice_rank_two (hV : Module.rank R V = 2)
    (Λ : Submodule (NormalizedOrder R)
      (FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V)))
    [Submodule.IsLattice (FractionRing R) Λ] :
    Module.rank (NormalizedOrder R) Λ = 2 := by
  rw [Submodule.IsLattice.rank' (FractionRing R), Module.rank_baseChange,
    Module.rank_baseChange, hV]
  simp

set_option maxHeartbeats 800000 in
-- Comparing the nested normalization and tensor instances requires additional elaboration.
/-- Every stable lattice in the normalized generic fibre of a hardly-ramified
three-adic representation is hardly ramified. All normalizing structures are
canonical instances from `NormalizedOrderData`. -/
@[nolint unusedArguments]
theorem hardlyRamified_of_stable_lattice (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (_N : NormalizedOrderData R)
    (Λ : Submodule (NormalizedOrder R)
      (FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V)))
    (hΛ : StableLattice.IsStableLattice
      ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R)).toRepresentation Λ) :
    let := hΛ.isLattice
    IsHardlyRamified (by decide : Odd 3) (normalized_lattice_rank_two hV Λ)
      (latticeGaloisRep ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R))
        Λ hΛ Topology.IsInducing.subtypeVal) := by
  exact hardlyRamified_of_integral_lattice (by decide) _ (hardlyRamified_normalization hV hρ)
    Λ hΛ Topology.IsInducing.subtypeVal (by
      let := hΛ.isLattice
      exact normalized_lattice_rank_two hV Λ)

set_option maxHeartbeats 800000 in
-- Comparing the nested normalization and tensor instances requires additional elaboration.
/-- The residue representation of every stable lattice in the normalized
generic fibre is hardly ramified and identifies with the Ribet reduction. -/
theorem hardlyRamified_reduction_of_stable_lattice (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (N : NormalizedOrderData R)
    (Λ : Submodule (NormalizedOrder R)
      (FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V)))
    (hΛ : StableLattice.IsStableLattice
      ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R)).toRepresentation Λ) :
    HardlyRamifiedReduction (by decide : Odd 3)
      ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R))
      Λ hΛ Topology.IsInducing.subtypeVal := by
  let := hΛ.isLattice
  have hdim := normalized_lattice_rank_two hV Λ
  have hHR := hardlyRamified_of_stable_lattice hV hρ N Λ hΛ
  exact hardlyRamified_lattice_reduction (O := NormalizedOrder R) (K := FractionRing R)
    (W := FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V))
    (p := 3) (by decide)
    ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R))
    Λ hΛ Topology.IsInducing.subtypeVal hdim hHR

end Normalization

end ThreeAdicPlan
