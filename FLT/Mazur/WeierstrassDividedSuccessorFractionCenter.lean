/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorFractionAlgebra
public import FLT.Mazur.WeierstrassDividedFirstFractionCenter

/-!
# Regular output centers on every successor fraction input

The actual flat input presentation supplies a regular denominator for the
full output center, including points on the exceptional fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a
local notation "D" => successorDividedInputCover hπ data j hj a
variable (t : Fin 3) (z : ((successorDividedInputCover hπ data j hj a).X
  (some (some t))).affineCover.I₀)
local notation "i" => Sigma.mk (some (some t)) z
local notation "C" => BlowupFractionChart.chart I (g t)

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

/-- The retained input denominator on an actual successor presentation. -/
def successorFractionDenominator : (U).X i :=
  successorFractionHom hπ data j hj a t z (BlowupFractionChart.denominator I (g t))

include ha in
/-- The entire output center is the ideal of the actual retained input denominator. -/
theorem successorFractionAlpha_center :
    (I).map (successorDividedAlpha hπ data j hj a i) =
      Ideal.span {successorFractionDenominator hπ data j hj a t z} := by
  exact WeierstrassSuccessiveX.successiveFractionAction_principal (S := (U).X i)
    W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6
    (by rw [← factor3_step hπ d e]; exact (d).factor3)
    (by rw [← factor4_step hπ d e]; exact (d).factor4)
    (by rw [← factor6_step hπ d e]; exact (d).factor6)
    (successorDividedParameter hπ data j hj a i)
    (successorFractionAlphaAlg hπ data j hj a t z ha) (successorFractionBetaAlg hπ data j hj a t z)
    (successorFractionAlg_parameter hπ data j hj a t z)
    (successorFractionAlg_addition hπ data j hj a t z ha)
    (WeierstrassSuccessiveX.successiveFractionPresentation_scale_regular (S := (U).X i)
      W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6 (g t)
      (successorFractionBetaAlg hπ data j hj a t z) (successorFractionHom hπ data j hj a t z)
      (successorFractionBetaAlg_factor hπ data j hj a t z)
      (successorFractionHom_flat hπ data j hj a t z)
      (IsRegular.of_ne_zero (pow_ne_zero _ hπ)))
    (g t) (hg t) (successorFractionHom hπ data j hj a t z)
    (successorFractionBetaAlg_factor hπ data j hj a t z)

/-- Its generator remains regular even on exceptional-fiber presentations. -/
theorem successorFractionDenominator_regular :
    IsRegular (successorFractionDenominator hπ data j hj a t z) :=
  flatRingHom_isRegular _ (successorFractionHom_flat hπ data j hj a t z)
    (BlowupFractionChart.denominator_regular I (g t))

include ha in
/-- Arbitrary affine restrictions retain the exact full output center. -/
theorem successorFractionAlpha_mapped_center {S : Type u} [CommRing S]
    (ψ : (U).X i →+* S) :
    (I).map (ψ.comp (successorDividedAlpha hπ data j hj a i)) =
      Ideal.span {ψ (successorFractionDenominator hπ data j hj a t z)} :=
  RegularCenter.mapped_center I _ _ (successorFractionAlpha_center hπ data j hj a t z ha) ψ

/-- Flat affine restrictions retain regularity of the same output generator. -/
theorem successorFractionDenominator_mapped_regular {S : Type u} [CommRing S]
    (ψ : (U).X i →+* S) (hψ : RingHom.Flat ψ) :
    IsRegular (ψ (successorFractionDenominator hπ data j hj a t z)) :=
  flatRingHom_isRegular ψ hψ (successorFractionDenominator_regular hπ data j hj a t z)

end FLT.Mazur.WeierstrassDividedDepth
