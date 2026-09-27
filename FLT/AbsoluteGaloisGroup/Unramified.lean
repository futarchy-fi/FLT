/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCompositum
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-!
# Arithmetic consequences of trivial local inertia

Compare inertia on a global subextension with inertia on its finite local compositum.
-/

@[expose] public section

open NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K

/-- Restricting local absolute inertia to a finite Galois subfield gives its full inertia. -/
lemma map_localInertiaGroup_eq_inertia
    (C : IntermediateField Kv (AlgebraicClosure Kv))
    [FiniteDimensional Kv C] [IsGalois Kv C] :
    (localInertiaGroup v).map (AlgEquiv.restrictNormalHom C) =
      (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).inertia Gal(C/Kv) := by
  let N : OpenNormalSubgroup (Field.absoluteGaloisGroup Kv) := {
    toSubgroup := C.fixingSubgroup
    isOpen' := (InfiniteGalois.isOpen_iff_finite C).mpr inferInstance
    isNormal' := (InfiniteGalois.normal_iff_isGalois C).mpr inferInstance }
  have h : ∀ (_ : IsGalois Kv (IntermediateField.fixedField C.fixingSubgroup)),
      (localInertiaGroup v).map
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField C.fixingSubgroup)) =
      (IsLocalRing.maximalIdeal (IntegralClosure Ov
        (IntermediateField.fixedField C.fixingSubgroup))).inertia
          Gal(IntermediateField.fixedField C.fixingSubgroup/Kv) := by
    intro
    exact map_localInertiaGroup_eq_finiteInertia v N
  rw [InfiniteGalois.fixedField_fixingSubgroup C] at h
  exact h inferInstance

namespace NumberField.InertiaComparison

/-- Trivial local inertia on the global field gives trivial inertia on the local compositum. -/
lemma localCompositum_inertia_eq_bot
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [Normal K L]
    (h : localInertiaGroup v ≤ (localRestriction v L).ker) :
    (IsLocalRing.maximalIdeal (IntegralClosure Ov (localCompositum v L))).inertia
      Gal(localCompositum v L/Kv) = ⊥ := by
  rw [← map_localInertiaGroup_eq_inertia, Subgroup.map_eq_bot_iff,
    IntermediateField.restrictNormalHom_ker, localCompositum_fixingSubgroup]
  exact h

end NumberField.InertiaComparison

/-- Torsion-free modules over a Dedekind domain are flat. -/
private lemma flatOfDedekindOfTorsionFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsDedekindDomain R] [Module.IsTorsionFree R M] : Module.Flat R M :=
  inferInstance

/-- Trivial inertia in a finite local Galois extension forces ramification index one. -/
lemma ramificationIdx_eq_one_of_inertia_eq_bot
    (C : IntermediateField Kv (AlgebraicClosure Kv))
    [FiniteDimensional Kv C] [IsGalois Kv C]
    (h : (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).inertia Gal(C/Kv) = ⊥) :
    (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).ramificationIdx Ov = 1 := by
  let B := IntegralClosure Ov C
  let P := IsLocalRing.maximalIdeal B
  let p := IsLocalRing.maximalIdeal Ov
  let : IsFractionRing B C := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension Kv C
  let : Module.Finite Ov B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.finite Ov Kv C (integralClosure Ov C)
  let : Module.IsTorsionFree Ov B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kv C).injective
    exact congrArg Subtype.val hxy
  let : Module.Flat Ov B :=
    @flatOfDedekindOfTorsionFree Ov B _ _ Algebra.toModule _ (by exact this)
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain Ov Kv C (integralClosure Ov C)
  let : P.LiesOver p := by dsimp only [P, p]; infer_instance
  let : SMulDistribClass Gal(C/Kv) B C := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(C/Kv) Ov B :=
    IsGaloisGroup.of_isFractionRing Gal(C/Kv) Ov B Kv C
  let : Finite (Ov ⧸ p) := inferInstanceAs (Finite (IsLocalRing.ResidueField Ov))
  let : Finite p.ResidueField := inferInstance
  let : PerfectField p.ResidueField := inferInstance
  calc
    P.ramificationIdx Ov = p.ramificationIdxIn B :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(C/Kv)).symm
    _ = Nat.card (P.inertia Gal(C/Kv)) := (Ideal.card_inertia_eq_ramificationIdxIn p P).symm
    _ = 1 := by rw [h]; simp


namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [Normal K L]

/-- Trivial local inertia gives ramification index one at the induced global prime. -/
lemma localInducedPrime_ramificationIdx_eq_one
    (h : localInertiaGroup v ≤ (localRestriction v L).ker) :
    (localInducedPrime v L).ramificationIdx (𝓞 K) = 1 := by
  obtain ⟨w, g, hw, hg⟩ := exists_inducedPrime_completion_embedding v L
  rw [hw, ramificationIdx_eq_of_completion_equiv v w (localCompositum v L)
    (completionEquivLocalCompositum v L w g hg)]
  exact ramificationIdx_eq_one_of_inertia_eq_bot v _ (localCompositum_inertia_eq_bot v L h)

/-- Trivial local inertia implies arithmetic unramifiedness at the induced global prime. -/
lemma localInducedPrime_isUnramifiedAt
    (h : localInertiaGroup v ≤ (localRestriction v L).ker) :
    Algebra.IsUnramifiedAt (𝓞 K) (localInducedPrime v L) := by
  exact Ideal.ramificationIdx_eq_one_iff.mp (localInducedPrime_ramificationIdx_eq_one v L h)

end NumberField.InertiaComparison

namespace NumberField.InertiaComparison
/-- If local inertia restricts trivially, every global prime above the place is unramified. -/
lemma isUnramifiedIn_of_localInertia_le_ker
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [Normal K L]
    (h : localInertiaGroup v ≤ (localRestriction v L).ker) :
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  let : IsGalois K L := {}
  let : SMulDistribClass Gal(L/K) (𝓞 L) L := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  intro P hP hPv
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(L/K),
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (localInducedPrime v L) Gal(L/K)]
  exact localInducedPrime_ramificationIdx_eq_one v L h

end NumberField.InertiaComparison
