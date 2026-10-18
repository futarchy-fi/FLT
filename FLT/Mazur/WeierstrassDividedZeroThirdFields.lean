/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondResidualRestriction

/-!
# The third fields of the actual depth-zero initial and closing residuals

Extract both entire errors from the simultaneously corrected second system.
The last node is shared, and both fields retain a single fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroSecondInitialRelativeEquiv
  arithmeticZeroSecondClosingEquiv laurentSystemNextField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- False selects the relative initial edge; true selects the complete closing edge. -/
def arithmeticZeroSecondTransition (closing b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if closing then (arithmeticZeroSecondClosingEquiv hπ data H j hj u hu m b).toAlgHom
  else (arithmeticZeroSecondInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticZeroSecondTransition hπ data H j hj u hu

/-- Both complete errors vanish at the proved second layer. -/
theorem arithmeticZeroSecondTransition_second (closing b : Bool) :
    E closing b 2 = AlgHom.id (Quotient R π 2) _ := by
  cases closing
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroSecondInitialRelativeEquiv_second hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroSecondClosingEquiv_second hπ data H j hj u hu b)

/-- Both full residuals respect the original coefficient quotient at every order. -/
theorem arithmeticZeroSecondTransition_restriction (closing b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E closing b (m + 1)).toRingHom =
      (E closing b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases closing
  · exact arithmeticZeroSecondInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticZeroSecondClosingEquiv_restriction hπ data H j hj u hu m b

/-- The whole third-layer coordinate error divided by its proved third parameter power. -/
def arithmeticZeroThirdField (closing b : Bool) : (Quotient R π 3)[T;T⁻¹] :=
  laurentSystemNextField (E closing b)
    (arithmeticZeroSecondTransition_restriction hπ data H j hj u hu closing b) 2
    (arithmeticZeroSecondTransition_second hπ data H j hj u hu closing b)

local notation "q" => arithmeticZeroThirdField hπ data H j hj u hu

/-- Every Laurent coefficient of the actual third error is recovered. -/
theorem arithmeticZeroThirdField_coordinate (closing b : Bool) :
    E closing b 3 (T 1) = T 1 + C (parameter R π 3 ^ 3) * q closing b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The complete third-layer residual is its constructed square-zero substitution. -/
theorem arithmeticZeroThirdField_subst (closing b : Bool) :
    E closing b 3 = LaurentSquareZeroAutomorphism.subst (parameter R π 3 ^ 3)
      (nextCorrectionParameter_square R π 2) (q closing b) :=
  laurentSystemNextField_subst _ _ _ _

/-- Lift each entire measured field once to the original integral ring. -/
def arithmeticZeroThirdIntegralField (closing b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 3 (q closing b)

/-- Both integral fields specialize to the entire measured third errors. -/
theorem arithmeticZeroThirdIntegralField_spec (closing b : Bool) :
    correctionField R π 3 (arithmeticZeroThirdIntegralField hπ data H j hj u hu closing b) =
      q closing b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.WeierstrassDividedDepth
