/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthResidualFifthOrder
public import FLT.Mazur.WeierstrassDividedFourthInitialFifthOrder
public import FLT.Mazur.WeierstrassDividedFourthOuterFifthOrder
public import FLT.Mazur.WeierstrassDividedFourthShallowFifthOrder
public import FLT.Mazur.WeierstrassDividedFourthFartherFifthOrder
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField

/-!
# Fifth-layer fields for every full fourth residual

Retain every interior and outer position, both corrected initial boundaries,
and the direct and reciprocal farther compensation. Every complete residual
supplies its own finite fifth-layer field and fixed integral lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false

/-- The full residual positions, including the original initial and outer neighbors. -/
inductive FourthResidualEdge
  | closing
  | incoming
  | preceding
  | initial
  | initialIncoming
  | outerIncoming
  | outerPreceding
  | shallow
  | shallowIncoming
  | fartherDirect
  | fartherIncoming

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Each actual edge residual is kept as its complete Laurent algebra map. -/
def arithmeticFourthJointTransition (edge : FourthResidualEdge) (b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  match edge with
  | .closing => (arithmeticFourthClosingEquiv hπ data H j hj u hu m b).toAlgHom
  | .incoming => (arithmeticFourthIncomingEquiv hπ data H j hj u hu m b).toAlgHom
  | .preceding => (arithmeticFourthPrecedingEquiv hπ data H j hj u hu m b).toAlgHom
  | .initial => (arithmeticFourthInitialRelativeEquiv hπ data H j hj u hu m b).toAlgHom
  | .initialIncoming =>
      (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu m b).toAlgHom
  | .outerIncoming => (arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu m b).toAlgHom
  | .outerPreceding => (arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu m b).toAlgHom
  | .shallow => (arithmeticFourthShallowRelativeEquiv hπ data H j hj u hu m b).toAlgHom
  | .shallowIncoming =>
      (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu m b).toAlgHom
  | .fartherDirect => (arithmeticFourthFartherOppositeEquiv hπ data H j hj u hu m b).toAlgHom
  | .fartherIncoming => (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu m b).toAlgHom

local notation "E" => arithmeticFourthJointTransition hπ data H j hj u hu

/-- Every complete relative residual vanishes at stage three. -/
theorem arithmeticFourthJointTransition_fourth (edge : FourthResidualEdge) (b : Bool) :
    E edge b 4 = AlgHom.id (Quotient R π 4) _ := by
  cases edge
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthClosingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthIncomingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthPrecedingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthInitialRelativeEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthInitialNeighborIncomingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthOuterIncomingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthOuterPrecedingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthShallowRelativeEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthShallowNeighborIncomingEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthFartherOppositeEquiv_fourth hπ data H j hj u hu b)
  · exact congrArg AlgEquiv.toAlgHom
      (arithmeticFourthFartherIncomingEquiv_fourth hπ data H j hj u hu b)

/-- All full substitutions respect the original full arithmetic quotient square. -/
theorem arithmeticFourthJointTransition_restriction
    (edge : FourthResidualEdge) (b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E edge b (m + 1)).toRingHom =
      (E edge b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases edge
  · exact arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthInitialRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthInitialNeighborIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthOuterIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthOuterPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthShallowRelativeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthShallowNeighborIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthFartherOppositeEquiv_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthFartherIncomingEquiv_restriction hπ data H j hj u hu m b

/-- The whole fifth-layer coordinate error divided by its proved fifth parameter power. -/
def arithmeticFifthResidualField (edge : FourthResidualEdge) (b : Bool) :
    (Quotient R π 5)[T;T⁻¹] :=
  laurentSystemNextField (E edge b)
    (arithmeticFourthJointTransition_restriction hπ data H j hj u hu edge b) 4
    (arithmeticFourthJointTransition_fourth hπ data H j hj u hu edge b)

local notation "q" => arithmeticFifthResidualField hπ data H j hj u hu

/-- Every term of the actual fifth-stage coordinate error is recovered. -/
theorem arithmeticFifthResidualField_coordinate (edge : FourthResidualEdge) (b : Bool) :
    E edge b 5 (T 1) = T 1 + C (parameter R π 5 ^ 5) * q edge b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The whole fifth-stage transition is its constructed square-zero substitution. -/
theorem arithmeticFifthResidualField_subst (edge : FourthResidualEdge) (b : Bool) :
    E edge b 5 = LaurentSquareZeroAutomorphism.subst (parameter R π 5 ^ 5)
      (nextCorrectionParameter_square R π 4) (q edge b) :=
  laurentSystemNextField_subst _ _ _ _

/-- One fixed integral lift keeps every coefficient of each of the fifth-layer fields. -/
def arithmeticFifthResidualIntegralField (edge : FourthResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 5 (q edge b)

/-- Each fixed lift specializes to its entire original finite Laurent field. -/
theorem arithmeticFifthResidualIntegralField_spec (edge : FourthResidualEdge) (b : Bool) :
    correctionField R π 5 (arithmeticFifthResidualIntegralField hπ data H j hj u hu edge b) =
      q edge b := integralCorrectionLift_spec R π _ _

/-- The scaled integral field supplies a whole-node correction input of order five. -/
def arithmeticFifthResidualCorrectionField (edge : FourthResidualEdge) (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4
    (arithmeticFifthResidualIntegralField hπ data H j hj u hu edge b)

/-- The correction input realizes the full residual in the node-construction convention. -/
theorem arithmeticFifthResidualCorrectionField_coordinate
    (edge : FourthResidualEdge) (b : Bool) :
    E edge b 5 (T 1) = T 1 + C (parameter R π 5) * correctionField R π 5
      (arithmeticFifthResidualCorrectionField hπ data H j hj u hu edge b) := by
  rw [arithmeticFifthResidualCorrectionField, correctionField_higher,
    arithmeticFifthResidualIntegralField_spec, ← mul_assoc, ← map_mul, ← pow_succ']
  exact arithmeticFifthResidualField_coordinate hπ data H j hj u hu edge b

end FLT.Mazur.WeierstrassDividedDepth
