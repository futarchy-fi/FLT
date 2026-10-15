/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentBranches
public import FLT.Mazur.WeierstrassSuccessiveInitialLaurentSlope
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra

/-!
# The original initial arithmetic root agrees with the first constructed branch

The root is computed from the initial divided coefficients at the actual
quotient order. Compatibility is proved from coefficient division, for both labels.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1)) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ k) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ d.b3) (hd4 : π ∣ d.b4) (hd6 : π ∣ d.b6)
  (he3 : π ∣ e.b3) (he4 : π ∣ e.b4) (he6 : π ∣ e.b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "v₀" => laurentBranchSlope (W.map q) (q (π ^ k)) (q (Data.b3 d))
  (q (Data.b4 d)) (q (Data.b6 d)) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m hd3) (arithmeticCoefficient_mem π m hd4)
  (arithmeticCoefficient_mem π m hd6)

include hπ in
/-- Both actual first-branch slopes equal the independently constructed initial arithmetic roots. -/
theorem arithmeticInitialBranchSlope (opposite : Bool) :
    rightIncidenceLaurent (q π)
      (arithmeticBranchSlope π m W (π ^ k) e.b3 e.b4 e.b6
        ha hs h2 he3 he4 he6 opposite) = v₀ opposite := by
  have h3 := factor3_step hπ d e
  have h4 := factor4_step hπ d e
  have h6 := factor6_step hπ d e
  cases opposite
  · simp only [arithmeticBranchSlope, laurentBranchSlope, Bool.false_eq_true, ↓reduceIte]
    have H := initialLaurent_nilpotentSlope (q π) (W.map q) (q (π ^ k))
      (q e.b3) (q e.b4) (q e.b6) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
      (arithmeticCoefficient_mem π m he6)
    simpa only [h3, h4, h6, map_mul, map_pow] using H
  · simp only [arithmeticBranchSlope, laurentBranchSlope, ↓reduceIte]
    have H := initialLaurent_oppositeSlope (q π) (W.map q) (q (π ^ k))
      (q e.b3) (q e.b4) (q e.b6) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
      (arithmeticCoefficient_mem π m he6)
    simpa only [h3, h4, h6, map_mul, map_pow] using H

end FLT.Mazur.WeierstrassDividedDepth
