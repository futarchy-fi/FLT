/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedChartIso
public import FLT.Mazur.WeierstrassRetainedFixedPuncturePreimage

/-!
# Full puncture preimages for the arithmetic retained isomorphisms

The constructed arithmetic isomorphisms preserve both original punctures,
at every retained depth and every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "C" => arithmeticRetainedFixedSmoothingIso data H m k hk a

/-- The entire outgoing open pulls back to the original outgoing open. -/
theorem arithmeticRetainedFixedSmoothingIso_left_preimage :
    (C).hom ⁻¹' Set.range (leftBranchOpen Q τ) = Set.range (leftBranchOpen Q t) :=
  retainedFixedSmoothingChart_left_preimage ..

/-- The entire incoming open pulls back to the original incoming open. -/
theorem arithmeticRetainedFixedSmoothingIso_right_preimage :
    (C).hom ⁻¹' Set.range (rightBranchOpen Q τ) = Set.range (rightBranchOpen Q t) :=
  retainedFixedSmoothingChart_right_preimage ..

end FLT.Mazur.WeierstrassDividedDepth
