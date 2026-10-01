/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FirstRamificationFiltration
public import Mathlib.GroupTheory.PGroup

/-!
# Finite first ramification groups are p-groups

Taking a p-th power increases the ramification congruence. Finite termination
therefore proves the p-group theorem without assuming any ramification conclusion.
-/

@[expose] public section

open IsLocalRing
namespace LocalRamification
variable (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [MulSemiringAction G R]
variable (p : ℕ) [CharP (ResidueField R) p]

/-- Taking a p-th power moves an automorphism one step down the filtration. -/
theorem ramificationGroup_pow_mem {i : ℕ} (hi : 1 ≤ i)
    {σ : G} (hσ : σ ∈ ramificationGroup R G i) :
    σ ^ p ∈ ramificationGroup R G (i + 1) := by
  let s : ramificationGroup R G i := ⟨σ, hσ⟩
  apply (mem_ramificationDifference_ker R G i hi (s ^ p)).mp
  change ramificationDifference R G i hi (s ^ p) = 1
  rw [map_pow]
  change (p • (fun x ↦ Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) (σ • x - x))) = 0
  funext x
  change p • Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) (σ • x - x) = 0
  rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
  have hp : (p : R) ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residue R (p : R) = 0
    simp
  simpa [pow_succ'] using Ideal.mul_mem_mul hp (hσ x)

/-- Repeated p-th powers move arbitrarily far down the filtration. -/
theorem ramificationGroup_pow_pow_mem {i : ℕ} (hi : 1 ≤ i)
    {σ : G} (hσ : σ ∈ ramificationGroup R G i) (n : ℕ) :
    σ ^ p ^ n ∈ ramificationGroup R G (i + n) := by
  induction n with
  | zero => simpa using hσ
  | succ n ih =>
    simpa [pow_succ, pow_mul, Nat.add_assoc] using
      ramificationGroup_pow_mem R G p (by omega : 1 ≤ i + n) ih

/-- The first group of a finite faithful action on a DVR is a p-group. -/
theorem firstGroup_isPGroup [Finite G] [FaithfulSMul G R] : IsPGroup p (firstGroup R G) := by
  obtain ⟨n, hn⟩ := exists_ramificationGroup_eq_bot R G
  intro σ
  refine ⟨n, Subtype.ext ?_⟩
  have h := ramificationGroup_pow_pow_mem R G p (by omega : 1 ≤ 1) σ.2 n
  have h' := ramificationGroup_antitone R G (by omega : n ≤ 1 + n) h
  rwa [hn, Subgroup.mem_bot] at h'

/-- First ramification descends through an injective local equivariant ring map. -/
theorem firstGroup_restrict {S H : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Group H] [MulSemiringAction H S]
    [Finite (ResidueField R)] (j : R →+* S) [IsLocalHom j] (hj : Function.Injective j)
    (f : H →* G) (heq : ∀ σ x, j (f σ • x) = σ • j x)
    {σ : H} (hσ : σ ∈ firstGroup S H) : f σ ∈ firstGroup R G := by
  have hres (x : R) : residue R (f σ • x - x) = 0 := by
    apply (ResidueField.map j).injective
    rw [map_zero, ResidueField.map_residue, map_sub, heq]
    exact (residue_eq_zero_iff _).mpr (firstGroup_le_inertia S H hσ (j x))
  let τ : ramificationGroup R G 0 := ⟨f σ, fun x ↦ by
    simpa [pow_one] using (residue_eq_zero_iff _).mp (hres x)⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply (mem_next_iff_uniformizer R G hπ 0 τ).mpr
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hπ
    (hπ.map (MulSemiringAction.toRingAut G R (f σ)))
  change π * (u : R) = f σ • π at hu
  obtain ⟨z, hz, hzres⟩ := firstGroup_ratio hσ (show j π ≠ 0 from by simpa using hj.ne hπ.ne_zero)
  have hju : j (u : R) = z := by
    apply mul_left_cancel₀ (show j π ≠ 0 from by simpa using hj.ne hπ.ne_zero)
    rw [← map_mul, hu, heq, hz, mul_comm]
  have huRes : residue R (u : R) = 1 := by
    apply (ResidueField.map j).injective
    rw [map_one, ResidueField.map_residue, hju, hzres]
  have hu1 : (u : R) - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, huRes, map_one, sub_self]
  change f σ • π - π ∈ maximalIdeal R ^ 2
  rw [← hu, ← mul_sub_one, pow_two]
  exact Ideal.mul_mem_mul hπ.not_isUnit hu1

open NumberField
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

/-- Open normal subgroups cut out finite extensions. -/
local instance finiteFixedField_finiteDimensional (N : OpenNormalSubgroup Γ) :
    FiniteDimensional Kv (IntermediateField.fixedField N.1.1) := by
  rw [← InfiniteGalois.isOpen_iff_finite,
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup Γ)]
  exact N.isOpen'

set_option synthInstance.maxHeartbeats 100000 in
-- The local integral-closure lies-over instance needs additional search time.
/-- The integers at a finite Galois level form a DVR. -/
local instance finiteIntegers_isDVR (N : OpenNormalSubgroup Γ) :
    IsDiscreteValuationRing (IntegralClosure O (IntermediateField.fixedField N.1.1)) := by
  let L := IntermediateField.fixedField N.1.1
  let D := IntegralClosure O L
  let : IsDedekindDomain D := by
    change IsDedekindDomain (integralClosure O L)
    exact IsIntegralClosure.isDedekindDomain O Kv L (integralClosure O L)
  let : (maximalIdeal D).LiesOver (maximalIdeal O) := inferInstance
  refine { not_a_field' := ?_ }
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) (maximalIdeal D)

set_option maxHeartbeats 1000000 in
-- Elaborating the integral-closure and Galois-action instances needs a larger budget.
set_option synthInstance.maxHeartbeats 100000 in
/-- The first group at every finite Galois level is a p-group.
The prime binder retains the residue-characteristic interface of the source theorem. -/
@[nolint unusedArguments]
theorem finite_firstGroup_isPGroup
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    (N : OpenNormalSubgroup Γ) :
    IsPGroup p
      (firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
        Gal(IntermediateField.fixedField N.1.1/Kv)) := by
  let L := IntermediateField.fixedField N.1.1
  let D := IntegralClosure O L
  let : IsFractionRing D L := by
    change IsFractionRing (integralClosure O L) L
    exact integralClosure.isFractionRing_of_finite_extension Kv L
  let : SMulDistribClass Gal(L/Kv) D L := ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(L/Kv) O D :=
    IsGaloisGroup.of_isFractionRing Gal(L/Kv) O D Kv L
  let : FaithfulSMul Gal(L/Kv) D := IsGaloisGroup.faithful O
  let : CharP (ResidueField D) p :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O D)).injective p
  exact firstGroup_isPGroup D Gal(L/Kv) p

/-- The ambient restriction homomorphism for two finite Galois levels. -/
noncomputable def finiteTowerRestriction {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    Gal(IntermediateField.fixedField N.1.1/Kv) →*
      Gal(IntermediateField.fixedField M.1.1/Kv) := by
  let j := IntermediateField.inclusion (IntermediateField.fixedField_antitone h)
  let := j.toAlgebra
  let : IsScalarTower Kv (IntermediateField.fixedField M.1.1)
      (IntermediateField.fixedField N.1.1) := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom (IntermediateField.fixedField M.1.1)

/-- Restricting an absolute inertia element through a tower gives its smaller coordinate. -/
theorem finiteTowerRestriction_comp {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    (finiteTowerRestriction v h).comp (finiteRestriction v N) = finiteRestriction v M := by
  let j := IntermediateField.inclusion (IntermediateField.fixedField_antitone h)
  let := j.toAlgebra
  let : IsScalarTower Kv (IntermediateField.fixedField M.1.1)
      (IntermediateField.fixedField N.1.1) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (IntermediateField.fixedField M.1.1)
      (IntermediateField.fixedField N.1.1) (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq' rfl
  ext σ : 1
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
    (IntermediateField.fixedField M.1.1) (IntermediateField.fixedField N.1.1) σ.1).symm

set_option maxHeartbeats 1000000 in
-- Finite residue fields and integral-closure towers require additional elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Restriction through a finite Galois tower preserves first ramification. -/
theorem finite_firstGroup_restrict {N M : OpenNormalSubgroup Γ} (h : N ≤ M)
    {σ : Gal(IntermediateField.fixedField N.1.1/Kv)}
    (hσ : σ ∈ firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv)) :
    finiteTowerRestriction v h σ ∈
      firstGroup (IntegralClosure O (IntermediateField.fixedField M.1.1))
        Gal(IntermediateField.fixedField M.1.1/Kv) := by
  let L := IntermediateField.fixedField N.1.1
  let E := IntermediateField.fixedField M.1.1
  let B := IntegralClosure O L
  let D := IntegralClosure O E
  let : Module.Finite O D := by
    change Module.Finite O (integralClosure O E)
    exact IsIntegralClosure.finite O Kv E (integralClosure O E)
  let : Ring.HasFiniteQuotients O := {
    finiteQuotient := by
      intro I hI
      obtain ⟨n, rfl⟩ := exists_maximalIdeal_pow_eq_of_principal O
        (IsPrincipalIdealRing.principal (maximalIdeal O)) I hI
      exact
        IsLocalRing.instFiniteQuotientIdealHPowNatMaximalIdealOfIsNoetherianRingOfResidueField n }
  let : Ring.HasFiniteQuotients D := Ring.HasFiniteQuotients.of_module_finite O D
  let : Finite (ResidueField D) :=
    Ring.HasFiniteQuotients.finiteQuotient (IsDiscreteValuationRing.not_a_field D)
  let j := IntermediateField.inclusion (IntermediateField.fixedField_antitone h)
  let i : D →+* B := IntegralClosure.map (j.restrictScalars O)
  let : Algebra D B := i.toAlgebra
  let : IsScalarTower O D B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsIntegral D B := ⟨fun x ↦
    (Algebra.IsIntegral.isIntegral (R := O) x).tower_top⟩
  let : FaithfulSMul D B := (faithfulSMul_iff_algebraMap_injective D B).mpr
    (IntegralClosure.map_injective _ j.injective)
  let : IsLocalHom i := inferInstanceAs (IsLocalHom (algebraMap D B))
  apply firstGroup_restrict D Gal(E/Kv) i (IntegralClosure.map_injective _ j.injective)
    (finiteTowerRestriction v h) (fun τ x ↦ ?_) hσ
  apply Subtype.ext
  let := j.toAlgebra
  let : IsScalarTower Kv E L := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormal_commutes τ E x.1

/-- The transition homomorphism between finite first groups, using proved stability. -/
noncomputable def finiteFirstTowerRestriction {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv) →*
    firstGroup (IntegralClosure O (IntermediateField.fixedField M.1.1))
      Gal(IntermediateField.fixedField M.1.1/Kv) :=
  ((finiteTowerRestriction v h).domRestrict _).codRestrict _ fun σ ↦
    finite_firstGroup_restrict v h σ.2

end LocalRamification
