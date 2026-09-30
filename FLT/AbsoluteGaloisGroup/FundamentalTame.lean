/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootInertiaTransitivity
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.Mathlib.RingTheory.Valuation.RootLifting
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Surjectivity of reduced uniformizer-root characters

Lifting a residue root of unity and inertia transitivity give surjectivity.
Wild inertia is defined by the first ramification congruence at every finite
Galois level. A DVR calculation makes each character descend to its quotient.
The finite first groups being p-groups and the explicit inverse-limit comparison
are separate remaining results.
-/

@[expose] public section

open NumberField Polynomial IsLocalRing

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => IntegralClosure O Ω
local notation "k" => ResidueField A

/-- Every residue root of unity lifts to an integral root of unity. -/
theorem exists_integral_root_of_unity {n : ℕ} (hn : 0 < n) (u : rootsOfUnity n k) :
    ∃ z : A, z ^ n = 1 ∧ residue A z = (u.1 : k) := by
  let B := localClosureValuation v
  let e : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let eRes := ResidueField.mapEquiv e
  let f : B[X] := X ^ n - 1
  have hf : f.map (residue B) ≠ 0 := by
    simpa [f] using X_pow_sub_C_ne_zero hn (1 : ResidueField B)
  have hu : eRes (u.1 : k) ^ n = 1 := by
    rw [← map_pow, (mem_rootsOfUnity' n u.1).mp u.2, map_one]
  obtain ⟨z, hz, hzu⟩ := B.exists_root_lifting f hf
    (eRes (u.1 : k)) (by simpa [f, IsRoot] using sub_eq_zero.mpr hu)
  refine ⟨e.symm z, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, e.apply_symm_apply, map_one]
    simpa [f, IsRoot, sub_eq_zero] using hz
  · apply eRes.injective
    change residue B (e (e.symm z)) = eRes (u.1 : k)
    rw [e.apply_symm_apply]
    exact hzu

variable {n : ℕ} (hn : 0 < n) {π : O}
  (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
  {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)

/-- Restrict the reduced character to the roots of unity of its degree. -/
noncomputable def rootCharacterToRoots (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) : localInertiaGroup v →* rootsOfUnity n k :=
  (character v hn
    (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
      hπ (Subtype.ext h)) hα).codRestrict _ fun σ ↦
        (mem_rootsOfUnity _ _).mpr (character_pow v hn _ hα σ)

/-- The reduced character of a uniformizer root is surjective onto residue roots of unity. -/
theorem rootCharacterToRoots_surjective (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    Function.Surjective (rootCharacterToRoots v hn hπ hα) := by
  intro u
  obtain ⟨z, hz, hzu⟩ := exists_integral_root_of_unity v hn u
  have hzval : z.1 ^ n = 1 := congrArg Subtype.val hz
  have ha : π.1 ≠ 0 := fun h ↦
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hπ (Subtype.ext h)
  have hα0 := root_ne_zero v hn ha hα
  obtain ⟨σ, hσ⟩ := inertia_transitive v hπ hn hα
    (show (z.1 * α) ^ n = algebraMap Kv Ω π.1 by rw [mul_pow, hzval, one_mul, hα])
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change residue A (integralRatio v hn ha hα σ) = (u.1 : k)
  rw [← hzu]
  congr 1
  apply Subtype.ext
  change σ.1 α / α = z.1
  rw [hσ, mul_div_cancel_right₀ _ hα0]

/-- The finite character quotient is canonically the residue roots of unity. -/
noncomputable def rootCharacterQuotientEquiv (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    localInertiaGroup v ⧸ (rootCharacterToRoots v hn hπ hα).ker ≃* rootsOfUnity n k :=
  QuotientGroup.quotientKerEquivOfSurjective (rootCharacterToRoots v hn hπ hα)
    (rootCharacterToRoots_surjective v hn hπ hα)

end LocalRoot

namespace LocalRamification

open scoped Pointwise

/-- Automorphisms acting trivially modulo the square of the maximal ideal.
For the integer ring of a finite local extension this is the first ramification group. -/
def firstGroup (R G : Type*) [CommRing R] [IsLocalRing R] [Group G]
    [MulSemiringAction G R] : Subgroup G :=
  ((maximalIdeal R) ^ 2).inertia G

/-- The defining congruence for the first ramification group. -/
theorem mem_firstGroup_iff {R G : Type*} [CommRing R] [IsLocalRing R] [Group G]
    [MulSemiringAction G R] (σ : G) :
    σ ∈ firstGroup R G ↔ ∀ x : R, σ • x - x ∈ maximalIdeal R ^ 2 := Iff.rfl

/-- The first ramification group is normal because the maximal ideal is characteristic. -/
instance firstGroup_normal (R G : Type*) [CommRing R] [IsLocalRing R] [Group G]
    [MulSemiringAction G R] : (firstGroup R G).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  have hm : g • maximalIdeal R = maximalIdeal R :=
    IsLocalRing.map_ringEquiv_maximalIdeal (MulSemiringAction.toRingAut G R g)
  have hp : g • (maximalIdeal R ^ 2) = maximalIdeal R ^ 2 := by rw [smul_pow', hm]
  exact (Ideal.inertia_smul g (maximalIdeal R ^ 2)).symm.trans
    (congrArg (Ideal.inertia G) hp)

/-- First ramification implies inertia. -/
theorem firstGroup_le_inertia (R G : Type*) [CommRing R] [IsLocalRing R] [Group G]
    [MulSemiringAction G R] : firstGroup R G ≤ (maximalIdeal R).inertia G := by
  intro σ hσ x
  exact (Ideal.pow_le_self (by omega : 2 ≠ 0)) (hσ x)

/-- A first-ramification automorphism multiplies every nonzero integer by a residue-one unit. -/
theorem firstGroup_ratio {R G : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Group G] [MulSemiringAction G R]
    {σ : G} (hσ : σ ∈ firstGroup R G) {x : R} (hx : x ≠ 0) :
    ∃ z : R, σ • x = z * x ∧ residue R z = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hsπ : Irreducible (σ • π) := hπ.map (MulSemiringAction.toRingAut G R σ)
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hπ hsπ
  have huRes : residue R (u : R) = 1 := by
    have hd := hσ π
    change σ • π - π ∈ maximalIdeal R ^ 2 at hd
    rw [← hu, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hd
    obtain ⟨t, ht⟩ := hd
    have hu1 : (u : R) - 1 = π * t := by
      apply mul_left_cancel₀ hπ.ne_zero
      simpa [mul_sub, pow_two, mul_assoc] using ht
    apply sub_eq_zero.mp
    rw [← map_one (residue R), ← map_sub, hu1, map_mul,
      (residue_eq_zero_iff π).mpr hπ.not_isUnit, zero_mul]
  obtain ⟨r, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  refine ⟨(σ • (w : R)) * (w⁻¹ : Rˣ) * (u : R) ^ r, ?_, ?_⟩
  · rw [smul_mul', smul_pow', ← hu, mul_pow]
    have hw : ((w⁻¹ : Rˣ) : R) * w = 1 := Units.inv_mul w
    calc
      (σ • (w : R)) * (π ^ r * (u : R) ^ r) =
          (σ • (w : R)) * (π ^ r * (u : R) ^ r) *
            (((w⁻¹ : Rˣ) : R) * w) := by rw [hw, mul_one]
      _ = _ := by ring
  · have hwres : residue R (σ • (w : R)) = residue R (w : R) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (residue_eq_zero_iff _).mpr (firstGroup_le_inertia R G hσ (w : R))
    rw [map_mul, map_mul, map_pow, hwres, huRes, one_pow, mul_one,
      ← map_mul, Units.mul_inv, map_one]

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "Γ" => Field.absoluteGaloisGroup Kv

/-- Restrict absolute inertia to a finite Galois subextension. -/
noncomputable def finiteRestriction (N : OpenNormalSubgroup Γ) :
    localInertiaGroup v →* Gal(IntermediateField.fixedField N.1.1/Kv) :=
  (AlgEquiv.restrictNormalHom (IntermediateField.fixedField N.1.1)).comp
    (localInertiaGroup v).subtype

/-- Wild inertia imposes the first ramification condition at every finite Galois level.
This is the subgroup in the absolute Galois inverse limit cut out by the finite first groups. -/
noncomputable def wildInertia : Subgroup (localInertiaGroup v) :=
  ⨅ N : OpenNormalSubgroup Γ,
    (firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv)).comap (finiteRestriction v N)

/-- Membership is the compatible family of finite first-ramification congruences. -/
theorem mem_wildInertia_iff (σ : localInertiaGroup v) :
    σ ∈ wildInertia v ↔ ∀ (N : OpenNormalSubgroup Γ)
      (x : IntegralClosure O (IntermediateField.fixedField N.1.1)),
      finiteRestriction v N σ • x - x ∈
        maximalIdeal (IntegralClosure O (IntermediateField.fixedField N.1.1)) ^ 2 := by
  simp only [wildInertia, Subgroup.mem_iInf, Subgroup.mem_comap, mem_firstGroup_iff]

/-- Wild inertia is normal in inertia. -/
instance wildInertia_normal : (wildInertia v).Normal := by
  apply Subgroup.normal_iInf_normal
  intro N
  infer_instance

/-- The full tame inertia quotient, before constructing its characters. -/
noncomputable abbrev tameInertia := localInertiaGroup v ⧸ wildInertia v

set_option maxHeartbeats 1000000 in
-- Finite Galois fields and integral-closure towers need extra elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Wild inertia kills every reduced uniformizer-root character. -/
theorem wildInertia_le_ker {n : ℕ} (hn : 0 < n) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    wildInertia v ≤ (LocalRoot.character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα).ker := by
  intro σ hσ
  let A := IntegralClosure O Ω
  have ha : π.1 ≠ 0 := fun h ↦
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hπ (Subtype.ext h)
  have hα0 := LocalRoot.root_ne_zero v hn ha hα
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (ContinuousSMulDiscrete.isOpen_stabilizer Γ α) (one_mem _)
  let L : IntermediateField Kv Ω := IntermediateField.fixedField N.1.1
  let : FiniteDimensional Kv L := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup Γ)]
    exact N.isOpen'
  let D := IntegralClosure O L
  let : IsDedekindDomain D := by
    change IsDedekindDomain (integralClosure O L)
    exact IsIntegralClosure.isDedekindDomain O Kv L (integralClosure O L)
  let : (maximalIdeal D).LiesOver (maximalIdeal O) := inferInstance
  let : IsDiscreteValuationRing D :=
    { not_a_field' := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) (maximalIdeal D) }
  let aL : L := ⟨α, fun g ↦ hN g.2⟩
  have haL : aL ^ n = algebraMap O L π := Subtype.ext hα
  let a : D := ⟨aL, IsIntegral.of_pow hn (by rw [haL]; exact isIntegral_algebraMap)⟩
  have ha0 : a ≠ 0 := fun h ↦ hα0 (congrArg (fun x : D ↦ ((x.1 : L) : Ω)) h)
  have hs : finiteRestriction v N σ ∈ firstGroup D Gal(L/Kv) :=
    (mem_wildInertia_iff v σ).mp hσ N
  obtain ⟨z, hz, hzres⟩ := firstGroup_ratio hs ha0
  let j : L →ₐ[O] Ω := L.val.restrictScalars O
  let i : D →+* A := IntegralClosure.map j
  let : Algebra D A := i.toAlgebra
  let : IsScalarTower O D A := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let : Algebra.IsIntegral D A := ⟨fun x ↦
    (Algebra.IsIntegral.isIntegral (R := O) x).tower_top⟩
  let : FaithfulSMul D A :=
    (faithfulSMul_iff_algebraMap_injective D A).mpr
      (IntegralClosure.map_injective j j.injective)
  let : IsLocalHom i := inferInstanceAs (IsLocalHom (algebraMap D A))
  have hres : residue A (i z) = 1 := by
    have := congrArg (ResidueField.map i) hzres
    simpa using this
  have hratio : LocalRoot.integralRatio v hn ha hα σ = i z := by
    apply Subtype.ext
    change σ.1 α / α = j z.1
    have he := congrArg (fun x : D ↦ j x.1) hz
    change j ((AlgEquiv.restrictNormalHom L σ.1) aL) = j z.1 * α at he
    rw [show j ((AlgEquiv.restrictNormalHom L σ.1) aL) = σ.1 α from
      AlgEquiv.restrictNormal_commutes σ.1 L aL] at he
    rw [he, mul_div_cancel_right₀ _ hα0]
  apply Units.ext
  change residue A (LocalRoot.integralRatio v hn ha hα σ) = 1
  rw [hratio, hres]

/-- The reduced root character descends to the full tame quotient. -/
noncomputable def tameRootCharacter {n : ℕ} (hn : 0 < n) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    tameInertia v →* rootsOfUnity n (ResidueField (IntegralClosure O Ω)) :=
  QuotientGroup.lift (wildInertia v) (LocalRoot.rootCharacterToRoots v hn hπ hα) (by
    intro σ hσ
    apply Subtype.ext
    exact wildInertia_le_ker v hn hπ hα hσ)

/-- Tame quotient root characters remain surjective. -/
theorem tameRootCharacter_surjective {n : ℕ} (hn : 0 < n) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    Function.Surjective (tameRootCharacter v hn hπ hα) := by
  intro u
  obtain ⟨σ, hσ⟩ := LocalRoot.rootCharacterToRoots_surjective v hn hπ hα u
  exact ⟨QuotientGroup.mk σ, hσ⟩

end LocalRamification
