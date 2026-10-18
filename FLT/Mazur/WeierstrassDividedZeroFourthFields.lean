/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdResidualRestriction

/-!
# The fourth fields of the actual depth-zero initial and closing residuals

Extract both entire errors from the simultaneously corrected third system.
The last node is shared, and both fields retain a single fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroThirdInitialRelativeEquiv
  arithmeticZeroThirdClosingEquiv laurentSystemNextField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- False selects the relative initial edge; true selects the complete closing edge. -/
def arithmeticZeroThirdTransition (closing b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if closing then (arithmeticZeroThirdClosingEquiv hπ data H j hj u hu m b).toAlgHom
  else (arithmeticZeroThirdInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticZeroThirdTransition hπ data H j hj u hu

/-- Both complete errors vanish at the proved third layer. -/
theorem arithmeticZeroThirdTransition_third (closing b : Bool) :
    E closing b 3 = AlgHom.id (Quotient R π 3) _ := by
  cases closing
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroThirdInitialRelativeEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroThirdClosingEquiv_third hπ data H j hj u hu b)

/-- Both full residuals respect the original coefficient quotient at every order. -/
theorem arithmeticZeroThirdTransition_restriction (closing b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E closing b (m + 1)).toRingHom =
      (E closing b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases closing
  · exact arithmeticZeroThirdInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticZeroThirdClosingEquiv_restriction hπ data H j hj u hu m b

/-- The whole fourth-layer coordinate error divided by its proved fourth parameter power. -/
def arithmeticZeroFourthField (closing b : Bool) : (Quotient R π 4)[T;T⁻¹] :=
  laurentSystemNextField (E closing b)
    (arithmeticZeroThirdTransition_restriction hπ data H j hj u hu closing b) 3
    (arithmeticZeroThirdTransition_third hπ data H j hj u hu closing b)

local notation "q" => arithmeticZeroFourthField hπ data H j hj u hu

/-- Every Laurent coefficient of the actual fourth error is recovered. -/
theorem arithmeticZeroFourthField_coordinate (closing b : Bool) :
    E closing b 4 (T 1) = T 1 + C (parameter R π 4 ^ 4) * q closing b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The complete fourth-layer residual is its constructed square-zero substitution. -/
theorem arithmeticZeroFourthField_subst (closing b : Bool) :
    E closing b 4 = LaurentSquareZeroAutomorphism.subst (parameter R π 4 ^ 4)
      (nextCorrectionParameter_square R π 3) (q closing b) :=
  laurentSystemNextField_subst _ _ _ _

/-- Lift each entire measured field once to the original integral ring. -/
def arithmeticZeroFourthIntegralField (closing b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 4 (q closing b)

/-- Both integral fields specialize to the entire measured fourth errors. -/
theorem arithmeticZeroFourthIntegralField_spec (closing b : Bool) :
    correctionField R π 4 (arithmeticZeroFourthIntegralField hπ data H j hj u hu closing b) =
      q closing b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.WeierstrassDividedDepth
