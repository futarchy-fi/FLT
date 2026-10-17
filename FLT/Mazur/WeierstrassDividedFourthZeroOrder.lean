/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroRestriction
public import FLT.Mazur.PolygonArithmeticCorrectionPunctureReduction
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField

/-!
# The first-order bound for the actual depth-zero initial residual

The complete four-round last factor reduces to identity on the residue layer.
Naturality then bounds every coefficient of its actual relative initial error.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "D" => fun m ↦ arithmeticFourthZeroInitialRelativeEquiv hπ data H m j hj u hu

/-- Both complete accumulated punctures reduce to identity on the original residue layer. -/
theorem arithmeticFourthAccumulatedLastPuncture_zero (b a : Bool) :
    arithmeticFourthAccumulatedLastPuncture hπ data H 0 j hj u hu b a = AlgEquiv.refl := by
  simp only [arithmeticFourthAccumulatedLastPuncture, arithmeticResidualLiftRetainedPuncture,
    correctionPunctureFactor_zero, twoBranchCorrectionPunctureFactor_zero]
  rfl

/-- The full relative initial error starts in the first parameter power. -/
theorem arithmeticFourthZeroInitialRelativeEquiv_zero (b : Bool) : D 0 b = AlgEquiv.refl := by
  dsimp only
  rw [arithmeticFourthZeroInitialRelativeEquiv_eq, arithmeticFourthAccumulatedLastPuncture_zero]

/-- Every Laurent coefficient of the full relative initial error is parameter-divisible. -/
theorem arithmeticFourthZeroInitialRelative_coeff_dvd (m : ℕ) (b : Bool)
    (z : (Quotient R π m)[T;T⁻¹]) (d : ℤ) :
    parameter R π m ∣ (D m b z - z).coeff d := by
  simpa only [Nat.zero_add, pow_one, AlgEquiv.coe_toAlgHom] using laurentSystem_error_coeff_dvd
    (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthZeroInitialRelativeEquiv_restriction hπ data H j hj u hu r b)
    (Nat.zero_le m)
    (congrArg AlgEquiv.toAlgHom (arithmeticFourthZeroInitialRelativeEquiv_zero
      hπ data H j hj u hu b)) z d

/-- The entire relative error, including all terms, belongs to the original coefficient ideal. -/
theorem arithmeticFourthZeroInitialRelative_sub_mem (m : ℕ) (b : Bool)
    (z : (Quotient R π m)[T;T⁻¹]) :
    D m b z - z ∈ (ideal (Quotient R π m) (parameter R π m)).map
      (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹]) := by
  simpa only [Nat.zero_add, Submodule.pow_one, AlgEquiv.coe_toAlgHom] using
    laurentSystem_error_sub_mem
    (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthZeroInitialRelativeEquiv_restriction hπ data H j hj u hu r b)
    (Nat.zero_le m)
    (congrArg AlgEquiv.toAlgHom (arithmeticFourthZeroInitialRelativeEquiv_zero
      hπ data H j hj u hu b)) z

end FLT.Mazur.WeierstrassDividedDepth
