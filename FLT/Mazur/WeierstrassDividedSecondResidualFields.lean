/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftSecondOrder
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField

/-!
# Constructed second residual fields for all four affected transitions

Each closing and incoming transition supplies its own full second-order
Laurent field. The fields lift once to integral coefficients and therefore
supply full node correction inputs at every subsequent arithmetic stage.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Keep incoming and closing residuals separately, on both original labeled branches. -/
def arithmeticResidualTransition (incoming b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if incoming then (arithmeticResidualLiftEdgeEquiv hπ data H m j hj u hu b false).toAlgHom
  else (arithmeticResidualLiftClosingEquiv hπ data H m j hj u hu b).toAlgHom

local notation "E" => arithmeticResidualTransition hπ data H j hj u hu

/-- Each of the four actual full transitions is identity at first order. -/
theorem arithmeticResidualTransition_first (incoming b : Bool) :
    E incoming b 1 = AlgHom.id (Quotient R π 1) _ := by
  cases incoming
  · change (arithmeticResidualLiftClosingEquiv hπ data H 1 j hj u hu b).toAlgHom = _
    rw [arithmeticResidualLiftClosingEquiv_first]
    rfl
  · change (arithmeticResidualLiftEdgeEquiv hπ data H 1 j hj u hu b false).toAlgHom = _
    rw [arithmeticResidualLiftEdgeEquiv_incoming_first]
    rfl

/-- Each transition retains the original full adjacent quotient square. -/
theorem arithmeticResidualTransition_restriction (incoming b : Bool) (m : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp (E incoming b (m + 1)).toRingHom =
      (E incoming b m).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  cases incoming
  · exact arithmeticResidualLiftClosingEquiv_restriction hπ data H m j hj u hu b
  · exact arithmeticResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b false

/-- The complete second-order field of each actual residual, with every Laurent term. -/
def arithmeticSecondResidualField (incoming b : Bool) : (Quotient R π 2)[T;T⁻¹] :=
  laurentSystemNextField (E incoming b)
    (arithmeticResidualTransition_restriction hπ data H j hj u hu incoming b) 1
    (arithmeticResidualTransition_first hπ data H j hj u hu incoming b)

local notation "q" => arithmeticSecondResidualField hπ data H j hj u hu

/-- Each field realizes the full coordinate error at the second arithmetic layer. -/
theorem arithmeticSecondResidualField_coordinate (incoming b : Bool) :
    E incoming b 2 (T 1) = T 1 + C (parameter R π 2 ^ 2) * q incoming b :=
  laurentSystemNextField_coordinate _ _ _ _

/-- The entire second-layer transition equals the constructed square-zero substitution. -/
theorem arithmeticSecondResidualField_subst (incoming b : Bool) :
    E incoming b 2 = LaurentSquareZeroAutomorphism.subst (parameter R π 2 ^ 2)
      (nextCorrectionParameter_square R π 1) (q incoming b) :=
  laurentSystemNextField_subst _ _ _ _

/-- One fixed integral lift for each of the four complete second residual fields. -/
def arithmeticSecondResidualIntegralField (incoming b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 2 (q incoming b)

/-- No coefficient is lost when specializing the integral lift back to its defining layer. -/
theorem arithmeticSecondResidualIntegralField_spec (incoming b : Bool) :
    correctionField R π 2 (arithmeticSecondResidualIntegralField hπ data H j hj u hu incoming b) =
      q incoming b := integralCorrectionLift_spec R π _ _

/-- The scaled integral field supplies a second-order whole-node correction input. -/
def arithmeticSecondResidualCorrectionField (incoming b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1
    (arithmeticSecondResidualIntegralField hπ data H j hj u hu incoming b)

/-- The actual second-order coordinate has exactly the scaled correction input convention. -/
theorem arithmeticSecondResidualCorrectionField_coordinate (incoming b : Bool) :
    E incoming b 2 (T 1) = T 1 + C (parameter R π 2) * correctionField R π 2
      (arithmeticSecondResidualCorrectionField hπ data H j hj u hu incoming b) := by
  rw [arithmeticSecondResidualCorrectionField, correctionField_higher,
    arithmeticSecondResidualIntegralField_spec, ← mul_assoc, ← map_mul, pow_one, ← pow_two]
  exact arithmeticSecondResidualField_coordinate hπ data H j hj u hu incoming b

end FLT.Mazur.WeierstrassDividedDepth
