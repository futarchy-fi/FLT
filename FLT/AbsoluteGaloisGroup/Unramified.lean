/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCompositum
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Algebra.Valued.LocallyCompact

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

