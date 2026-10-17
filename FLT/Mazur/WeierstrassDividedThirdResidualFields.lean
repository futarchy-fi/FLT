/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondPrecedingTransition
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField

/-!
# Third-layer fields for all six remaining full residuals

The closing, shared incoming, and predecessor incoming edges each retain
both labels. Their actual compatible full substitutions determine the next
finite fields and a fixed integral lift at every later arithmetic order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false

/-- The three affected edge positions on each labeled arm of the second atlas. -/
inductive SecondResidualEdge
  | closing
  | incoming
  | preceding

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Each actual edge residual is kept as its complete Laurent algebra map. -/
def arithmeticSecondJointTransition (edge : SecondResidualEdge) (b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  match edge with
  | .closing => (arithmeticSecondJointClosingEquiv hπ data H m j hj u hu b).toAlgHom
  | .incoming => (arithmeticSecondJointIncomingEquiv hπ data H m j hj u hu b).toAlgHom
  | .preceding => (arithmeticSecondPrecedingIncomingEquiv hπ data H m j hj u hu b).toAlgHom

local notation "E" => arithmeticSecondJointTransition hπ data H j hj u hu

/-- All six full residuals vanish at stage two. -/
theorem arithmeticSecondJointTransition_second (edge : SecondResidualEdge) (b : Bool) :
    E edge b 2 = AlgHom.id (Quotient R π 2) _ := by
  cases edge
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticSecondJointClosingEquiv_second hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticSecondJointIncomingEquiv_second hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticSecondPrecedingIncomingEquiv_second hπ data H j hj u hu b)

/-- All six substitutions respect the original full arithmetic quotient square. -/
theorem arithmeticSecondJointTransition_restriction
    (edge : SecondResidualEdge) (b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E edge b (m + 1)).toRingHom =
      (E edge b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases edge
  · exact arithmeticSecondJointClosingEquiv_restriction hπ data H m j hj u hu b
  · exact arithmeticSecondJointIncomingEquiv_restriction hπ data H m j hj u hu b
  · exact arithmeticSecondPrecedingIncomingEquiv_restriction hπ data H m j hj u hu b

/-- The whole third-layer coordinate error divided by its proved cubic parameter power. -/
def arithmeticThirdResidualField (edge : SecondResidualEdge) (b : Bool) :
    (Quotient R π 3)[T;T⁻¹] :=
  laurentSystemNextField (E edge b)
    (arithmeticSecondJointTransition_restriction hπ data H j hj u hu edge b) 2
    (arithmeticSecondJointTransition_second hπ data H j hj u hu edge b)

local notation "q" => arithmeticThirdResidualField hπ data H j hj u hu

/-- Every term of the actual third-stage coordinate error is recovered. -/
theorem arithmeticThirdResidualField_coordinate (edge : SecondResidualEdge) (b : Bool) :
    E edge b 3 (T 1) = T 1 + C (parameter R π 3 ^ 3) * q edge b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The whole third-stage transition is its constructed square-zero substitution. -/
theorem arithmeticThirdResidualField_subst (edge : SecondResidualEdge) (b : Bool) :
    E edge b 3 = LaurentSquareZeroAutomorphism.subst (parameter R π 3 ^ 3)
      (nextCorrectionParameter_square R π 2) (q edge b) :=
  laurentSystemNextField_subst _ _ _ _

/-- One fixed integral lift keeps every coefficient of each of the six third-layer fields. -/
def arithmeticThirdResidualIntegralField (edge : SecondResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 3 (q edge b)

/-- Each fixed lift specializes to its entire original finite Laurent field. -/
theorem arithmeticThirdResidualIntegralField_spec (edge : SecondResidualEdge) (b : Bool) :
    correctionField R π 3 (arithmeticThirdResidualIntegralField hπ data H j hj u hu edge b) =
      q edge b := integralCorrectionLift_spec R π _ _

/-- The scaled integral field supplies a whole-node correction input of order three. -/
def arithmeticThirdResidualCorrectionField (edge : SecondResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 2
    (arithmeticThirdResidualIntegralField hπ data H j hj u hu edge b)

/-- The correction input realizes the full residual in the node-construction convention. -/
theorem arithmeticThirdResidualCorrectionField_coordinate
    (edge : SecondResidualEdge) (b : Bool) :
    E edge b 3 (T 1) = T 1 + C (parameter R π 3) * correctionField R π 3
      (arithmeticThirdResidualCorrectionField hπ data H j hj u hu edge b) := by
  rw [arithmeticThirdResidualCorrectionField, correctionField_higher,
    arithmeticThirdResidualIntegralField_spec, ← mul_assoc, ← map_mul, ← pow_succ']
  exact arithmeticThirdResidualField_coordinate hπ data H j hj u hu edge b

end FLT.Mazur.WeierstrassDividedDepth
