/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Coefficient localization at the contracted prime

The actual tensor base change maps to the original ambient local ring. Both
scalar towers, the localization property, and the local coefficient map are
constructed from the condition that the ambient prime lies over the base prime.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace FLT.Mazur.FCurve
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
/-- The actual coefficient-localized ambient maps canonically to its local ring. -/
def primeCoefficientLift :
    (Localization.AtPrime p ⊗[R] B) →+* Localization.AtPrime q := by
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  exact (AlgHom.liftEquiv R (Localization.AtPrime p) B (Localization.AtPrime q)
    (IsScalarTower.toAlgHom R B (Localization.AtPrime q))).toRingHom

/-- The canonical map sends a pure tensor to the product of the two structure maps. -/
lemma primeCoefficientLift_tmul (s : Localization.AtPrime p) (b : B) :
    primeCoefficientLift p q (s ⊗ₜ[R] b) =
      Localization.localRingHom p q (algebraMap R B) Ideal.LiesOver.over s *
        algebraMap B (Localization.AtPrime q) b := by
  simp [primeCoefficientLift, Algebra.smul_def,
    Localization.AtPrime.algebraOfLiesOver, RingHom.algebraMap_toAlgebra]

/-- Compatibility with the original ambient algebra. -/
lemma primeCoefficientLift_tower_right :
    let _ := (primeCoefficientLift p q).toAlgebra
    IsScalarTower B (Localization.AtPrime p ⊗[R] B) (Localization.AtPrime q) := by
  let _ : Algebra B (Localization.AtPrime p ⊗[R] B) :=
    Algebra.TensorProduct.rightAlgebra
  let _ := (primeCoefficientLift p q).toAlgebra
  dsimp only
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change algebraMap B (Localization.AtPrime q) b = primeCoefficientLift p q (1 ⊗ₜ[R] b)
  rw [primeCoefficientLift_tmul, map_one, one_mul]
/-- Compatibility with the localized coefficient algebra. -/
lemma primeCoefficientLift_tower_left :
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    let _ := (primeCoefficientLift p q).toAlgebra
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] B)
      (Localization.AtPrime q) := by
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  let _ := (primeCoefficientLift p q).toAlgebra
  dsimp only
  apply IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime p)
    (S := Localization.AtPrime p ⊗[R] B) (A := Localization.AtPrime q)
  intro s
  change _ = primeCoefficientLift p q (s ⊗ₜ[R] 1)
  rw [primeCoefficientLift_tmul, map_one, mul_one]
  rfl

/-- The original prime complement still localizes the coefficient-changed ambient. -/
lemma primeCoefficientLift_isLocalization :
    let _ := (primeCoefficientLift p q).toAlgebra
    IsLocalization
      (q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R)
        (A := Localization.AtPrime p))) (Localization.AtPrime q) := by
  let _ := (primeCoefficientLift p q).toAlgebra
  let _ := primeCoefficientLift_tower_right p q
  apply IsLocalization.isLocalization_of_submonoid_le
    (Localization.AtPrime p ⊗[R] B) (Localization.AtPrime q)
    (Algebra.algebraMapSubmonoid B p.primeCompl) q.primeCompl
  rintro _ ⟨r, hr, rfl⟩
  change algebraMap R B r ∉ q
  exact fun h ↦ hr (Ideal.LiesOver.over (P := q) (p := p) ▸ h)

/-- The coefficient localization at the contracted prime maps locally to the ambient stalk. -/
lemma primeCoefficient_localHom :
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  change IsLocalHom (Localization.localRingHom p q (algebraMap R B) Ideal.LiesOver.over)
  infer_instance

end FLT.Mazur.FCurve
