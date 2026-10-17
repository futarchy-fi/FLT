/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroOrder

/-!
# The first field of the complete depth-zero initial error

Extract a finite Laurent field from the actual relative four-round residual.
Its fixed integral lift is ready for simultaneous initial and last corrections.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthZeroInitialRelativeEquiv laurentSystemNextField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "D" => fun m ↦ arithmeticFourthZeroInitialRelativeEquiv hπ data H m j hj u hu

/-- The whole first-layer coordinate error divided by its proved parameter factor. -/
def arithmeticFourthZeroFirstField (b : Bool) : (Quotient R π 1)[T;T⁻¹] :=
  laurentSystemNextField (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthZeroInitialRelativeEquiv_restriction hπ data H j hj u hu r b) 0
    (congrArg AlgEquiv.toAlgHom
      (arithmeticFourthZeroInitialRelativeEquiv_zero hπ data H j hj u hu b))

local notation "q" => arithmeticFourthZeroFirstField hπ data H j hj u hu

/-- Every term of the actual first-layer relative coordinate error is recovered. -/
theorem arithmeticFourthZeroFirstField_coordinate (b : Bool) :
    D 1 b (T 1) = T 1 + C (parameter R π 1) * q b := by
  have h : (D 1 b).toAlgHom (T 1) = T 1 + C (parameter R π 1 ^ 1) * q b :=
    laurentSystemNextField_coordinate (fun r ↦ (D r b).toAlgHom)
      (fun r ↦ arithmeticFourthZeroInitialRelativeEquiv_restriction hπ data H j hj u hu r b) 0
      (congrArg AlgEquiv.toAlgHom
        (arithmeticFourthZeroInitialRelativeEquiv_zero hπ data H j hj u hu b))
  simpa only [pow_one, AlgEquiv.coe_toAlgHom] using h

/-- The complete first-layer relative transition is its constructed square-zero substitution. -/
theorem arithmeticFourthZeroFirstField_subst (b : Bool) :
    (D 1 b).toAlgHom = LaurentSquareZeroAutomorphism.subst (parameter R π 1)
      (by simpa only [Nat.zero_add, pow_one] using nextCorrectionParameter_square R π 0) (q b) := by
  exact LaurentSquareZeroAutomorphism.eq_subst _ _ _ _
    (arithmeticFourthZeroFirstField_coordinate hπ data H j hj u hu b)

/-- One integral polynomial keeps every coefficient of the actual first relative field. -/
def arithmeticFourthZeroFirstIntegralField (b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 1 (q b)

/-- The fixed integral field specializes to the entire measured relative error. -/
theorem arithmeticFourthZeroFirstIntegralField_spec (b : Bool) :
    correctionField R π 1 (arithmeticFourthZeroFirstIntegralField hπ data H j hj u hu b) =
      q b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.WeierstrassDividedDepth
