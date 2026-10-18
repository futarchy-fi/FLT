/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthResidualRestriction

/-!
# The sixth fields of the actual depth-zero initial and closing residuals

Extract both entire errors from the simultaneously corrected fifth system.
The last node is shared, and both fields retain a single fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroFifthInitialRelativeEquiv
  arithmeticZeroFifthClosingEquiv laurentSystemNextField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- False selects the relative initial edge; true selects the complete closing edge. -/
def arithmeticZeroFifthTransition (closing b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if closing then (arithmeticZeroFifthClosingEquiv hπ data H j hj u hu m b).toAlgHom
  else (arithmeticZeroFifthInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticZeroFifthTransition hπ data H j hj u hu

/-- Both complete errors vanish at the proved fifth layer. -/
theorem arithmeticZeroFifthTransition_fifth (closing b : Bool) :
    E closing b 5 = AlgHom.id (Quotient R π 5) _ := by
  cases closing
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroFifthInitialRelativeEquiv_fifth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticZeroFifthClosingEquiv_fifth hπ data H j hj u hu b)

/-- Both full residuals respect the original coefficient quotient at every order. -/
theorem arithmeticZeroFifthTransition_restriction (closing b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E closing b (m + 1)).toRingHom =
      (E closing b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases closing
  · exact arithmeticZeroFifthInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticZeroFifthClosingEquiv_restriction hπ data H j hj u hu m b

/-- The whole sixth-layer coordinate error divided by its proved sixth parameter power. -/
def arithmeticZeroSixthField (closing b : Bool) : (Quotient R π 6)[T;T⁻¹] :=
  laurentSystemNextField (E closing b)
    (arithmeticZeroFifthTransition_restriction hπ data H j hj u hu closing b) 5
    (arithmeticZeroFifthTransition_fifth hπ data H j hj u hu closing b)

local notation "q" => arithmeticZeroSixthField hπ data H j hj u hu

/-- Every Laurent coefficient of the actual sixth error is recovered. -/
theorem arithmeticZeroSixthField_coordinate (closing b : Bool) :
    E closing b 6 (T 1) = T 1 + C (parameter R π 6 ^ 6) * q closing b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The complete sixth-layer residual is its constructed square-zero substitution. -/
theorem arithmeticZeroSixthField_subst (closing b : Bool) :
    E closing b 6 = LaurentSquareZeroAutomorphism.subst (parameter R π 6 ^ 6)
      (nextCorrectionParameter_square R π 5) (q closing b) :=
  laurentSystemNextField_subst _ _ _ _

/-- Lift each entire measured field once to the original integral ring. -/
def arithmeticZeroSixthIntegralField (closing b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 6 (q closing b)

/-- Both integral fields specialize to the entire measured sixth errors. -/
theorem arithmeticZeroSixthIntegralField_spec (closing b : Bool) :
    correctionField R π 6 (arithmeticZeroSixthIntegralField hπ data H j hj u hu closing b) =
      q closing b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.WeierstrassDividedDepth
