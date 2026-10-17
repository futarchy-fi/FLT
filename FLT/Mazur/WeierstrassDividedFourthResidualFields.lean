/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdResidualFourthOrder
public import FLT.Mazur.WeierstrassDividedThirdInitialFourthOrder
public import FLT.Mazur.WeierstrassDividedThirdEarlierFourthOrder
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField

/-!
# Fourth-layer fields for every full third residual

Retain the three interior edge positions, the relative original initial edge,
and both orientations of the further incoming edge. Every complete residual
supplies its own finite fourth-layer field and fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false

/-- The full residual positions, including the original initial and outer neighbors. -/
inductive ThirdResidualEdge
  | closing
  | incoming
  | preceding
  | initial
  | earlierDirect
  | earlierIncoming

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Each actual edge residual is kept as its complete Laurent algebra map. -/
def arithmeticThirdJointTransition (edge : ThirdResidualEdge) (b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  match edge with
  | .closing => (arithmeticThirdClosingEquiv hπ data H j hj u hu m b).toAlgHom
  | .incoming => (arithmeticThirdIncomingEquiv hπ data H j hj u hu m b).toAlgHom
  | .preceding => (arithmeticThirdPrecedingEquiv hπ data H j hj u hu m b).toAlgHom
  | .initial => (arithmeticThirdInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom
  | .earlierDirect => (arithmeticThirdEarlierOppositeEquiv hπ data H j hj u hu m b).toAlgHom
  | .earlierIncoming => (arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticThirdJointTransition hπ data H j hj u hu

/-- Every complete relative residual vanishes at stage three. -/
theorem arithmeticThirdJointTransition_third (edge : ThirdResidualEdge) (b : Bool) :
    E edge b 3 = AlgHom.id (Quotient R π 3) _ := by
  cases edge
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdClosingEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdIncomingEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdPrecedingEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdInitialRelativeEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdEarlierOppositeEquiv_third hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticThirdEarlierIncomingEquiv_third hπ data H j hj u hu b)

/-- All full substitutions respect the original full arithmetic quotient square. -/
theorem arithmeticThirdJointTransition_restriction
    (edge : ThirdResidualEdge) (b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E edge b (m + 1)).toRingHom =
      (E edge b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases edge
  · exact arithmeticThirdClosingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticThirdIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticThirdPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticThirdInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticThirdEarlierOppositeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticThirdEarlierIncomingEquiv_restriction hπ data H j hj u hu m b

/-- The whole fourth-layer coordinate error divided by its proved fourth parameter power. -/
def arithmeticFourthResidualField (edge : ThirdResidualEdge) (b : Bool) :
    (Quotient R π 4)[T;T⁻¹] :=
  laurentSystemNextField (E edge b)
    (arithmeticThirdJointTransition_restriction hπ data H j hj u hu edge b) 3
    (arithmeticThirdJointTransition_third hπ data H j hj u hu edge b)

local notation "q" => arithmeticFourthResidualField hπ data H j hj u hu

/-- Every term of the actual fourth-stage coordinate error is recovered. -/
theorem arithmeticFourthResidualField_coordinate (edge : ThirdResidualEdge) (b : Bool) :
    E edge b 4 (T 1) = T 1 + C (parameter R π 4 ^ 4) * q edge b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The whole fourth-stage transition is its constructed square-zero substitution. -/
theorem arithmeticFourthResidualField_subst (edge : ThirdResidualEdge) (b : Bool) :
    E edge b 4 = LaurentSquareZeroAutomorphism.subst (parameter R π 4 ^ 4)
      (nextCorrectionParameter_square R π 3) (q edge b) :=
  laurentSystemNextField_subst _ _ _ _

/-- One fixed integral lift keeps every coefficient of each of the fourth-layer fields. -/
def arithmeticFourthResidualIntegralField (edge : ThirdResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 4 (q edge b)

/-- Each fixed lift specializes to its entire original finite Laurent field. -/
theorem arithmeticFourthResidualIntegralField_spec (edge : ThirdResidualEdge) (b : Bool) :
    correctionField R π 4 (arithmeticFourthResidualIntegralField hπ data H j hj u hu edge b) =
      q edge b := integralCorrectionLift_spec R π _ _

/-- The scaled integral field supplies a whole-node correction input of order four. -/
def arithmeticFourthResidualCorrectionField (edge : ThirdResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3
    (arithmeticFourthResidualIntegralField hπ data H j hj u hu edge b)

/-- The correction input realizes the full residual in the node-construction convention. -/
theorem arithmeticFourthResidualCorrectionField_coordinate
    (edge : ThirdResidualEdge) (b : Bool) :
    E edge b 4 (T 1) = T 1 + C (parameter R π 4) * correctionField R π 4
      (arithmeticFourthResidualCorrectionField hπ data H j hj u hu edge b) := by
  rw [arithmeticFourthResidualCorrectionField, correctionField_higher,
    arithmeticFourthResidualIntegralField_spec, ← mul_assoc, ← map_mul, ← pow_succ']
  exact arithmeticFourthResidualField_coordinate hπ data H j hj u hu edge b

end FLT.Mazur.WeierstrassDividedDepth
