/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstResidualRestriction

/-!
# The second fields of the actual depth-zero initial and closing residuals

Extract both entire errors from the simultaneously corrected first system.
The last node is shared, and both fields retain a single fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroFirstInitialRelativeEquiv
  arithmeticZeroFirstClosingEquiv laurentSystemNextField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- False selects the relative initial edge; true selects the complete closing edge. -/
def arithmeticZeroFirstTransition (closing b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if closing then (arithmeticZeroFirstClosingEquiv hπ data H j hj u hu m b).toAlgHom
  else (arithmeticZeroFirstInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticZeroFirstTransition hπ data H j hj u hu

/-- Both complete errors vanish at the proved first layer. -/
theorem arithmeticZeroFirstTransition_first (closing b : Bool) :
    E closing b 1 = AlgHom.id (Quotient R π 1) _ := by
  cases closing
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroFirstInitialRelativeEquiv_first hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroFirstClosingEquiv_first hπ data H j hj u hu b)

/-- Both full residuals respect the original coefficient quotient at every order. -/
theorem arithmeticZeroFirstTransition_restriction (closing b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E closing b (m + 1)).toRingHom =
      (E closing b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases closing
  · exact arithmeticZeroFirstInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticZeroFirstClosingEquiv_restriction hπ data H j hj u hu m b

/-- The whole second-layer coordinate error divided by its proved second parameter power. -/
def arithmeticZeroSecondField (closing b : Bool) : (Quotient R π 2)[T;T⁻¹] :=
  laurentSystemNextField (E closing b)
    (arithmeticZeroFirstTransition_restriction hπ data H j hj u hu closing b) 1
    (arithmeticZeroFirstTransition_first hπ data H j hj u hu closing b)

local notation "q" => arithmeticZeroSecondField hπ data H j hj u hu

/-- Every Laurent coefficient of the actual second error is recovered. -/
theorem arithmeticZeroSecondField_coordinate (closing b : Bool) :
    E closing b 2 (T 1) = T 1 + C (parameter R π 2 ^ 2) * q closing b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The complete second-layer residual is its constructed square-zero substitution. -/
theorem arithmeticZeroSecondField_subst (closing b : Bool) :
    E closing b 2 = LaurentSquareZeroAutomorphism.subst (parameter R π 2 ^ 2)
      (nextCorrectionParameter_square R π 1) (q closing b) :=
  laurentSystemNextField_subst _ _ _ _

/-- Lift each entire measured field once to the original integral ring. -/
def arithmeticZeroSecondIntegralField (closing b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 2 (q closing b)

/-- Both integral fields specialize to the entire measured next errors. -/
theorem arithmeticZeroSecondIntegralField_spec (closing b : Bool) :
    correctionField R π 2 (arithmeticZeroSecondIntegralField hπ data H j hj u hu closing b) =
      q closing b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.WeierstrassDividedDepth
