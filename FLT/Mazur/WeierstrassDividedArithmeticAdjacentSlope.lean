/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveAdjacentLaurentSlope
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra

/-!
# Both actual divided arithmetic slopes agree on their original adjacent edge

The original divided coefficients and powers determine the two roots.
Their Laurent compatibility is proved at every quotient order, retaining
the same small or opposite branch label on the two consecutive charts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) (k : ℕ)
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1)) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ k) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ d.b3) (hd4 : π ∣ d.b4) (hd6 : π ∣ d.b6)
  (he3 : π ∣ e.b3) (he4 : π ∣ e.b4) (he6 : π ∣ e.b6)
  (hsNext : π ∣ π ^ (k + 1))
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

include hπ in
/-- Both genuine arithmetic slopes retain their labels on the original inverse Laurent edge. -/
theorem arithmeticAdjacentBranchSlope (opposite : Bool) :
    inverseLeftIncidenceLaurent (q π)
      (arithmeticBranchSlope π m W (π ^ k) d.b3 d.b4 d.b6
        ha hs h2 hd3 hd4 hd6 opposite) =
    rightIncidenceLaurent (q π)
      (arithmeticBranchSlope π m W (π ^ (k + 1)) e.b3 e.b4 e.b6
        ha hsNext h2 he3 he4 he6 opposite) := by
  have h3 := factor3_step hπ d e
  have h4 := factor4_step hπ d e
  have h6 := factor6_step hπ d e
  cases opposite
  · simp only [arithmeticBranchSlope, Bool.false_eq_true, ↓reduceIte]
    have h := adjacentLaurent_nilpotentSlope (q π) J (W.map q) (q (π ^ k))
      (q e.b3) (q e.b4) (q e.b6) (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
      (arithmeticCoefficient_mem π m he6)
    simpa only [h3, h4, h6, pow_succ π k, map_mul, map_pow] using h
  · simp only [arithmeticBranchSlope, ↓reduceIte]
    have h := adjacentLaurent_oppositeSlope (q π) J (W.map q) (q (π ^ k))
      (q e.b3) (q e.b4) (q e.b6) (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
      (arithmeticCoefficient_mem π m he6)
    simpa only [h3, h4, h6, pow_succ π k, map_mul, map_pow] using h

end FLT.Mazur.WeierstrassDividedDepth
