/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSeparatedBoundaryReversed

/-!
# Boundary-depth contracts for the full separated pair cover

At middle depth or the next odd depth, both unshifted and singly shifted
formulas fit the final stage. Thus the full cover needs no extra stage bound.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Both actual output depths fit the final atlas at either boundary depth. -/
theorem arithmeticLastRetainedSeparatedBoundary_stage (i j depth : ℕ)
    (hupper : depth ≤ 2 * (j + 2) + 1) :
    max (min (i + j + 2) (depth - (i + j + 2)))
      (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2 := by
  omega

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i j : ℕ) (hk : j + 2 ≤ n) (hgap : i + 1 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hupper : depth ≤ 2 * (j + 2) + 1)
  (hgen : IsLocalRing.maximalIdeal R = ideal R π)

local notation "A" => arithmeticLastRetainedSeparatedBoundarySmoothOpen node data m i j hk
local notation "B" => arithmeticLastRetainedSeparatedBoundaryReversedSmoothOpen node data m i j hk

/-- The full separated boundary cover in increasing creation order. -/
def arithmeticLastRetainedSeparatedBoundaryDepthCover : (A).toScheme.OpenCover :=
  arithmeticLastRetainedSeparatedBoundarySmoothCover node data m i j hk hgap hdepth
    (by omega) (arithmeticLastRetainedSeparatedBoundary_stage i j depth hupper) hgen

/-- The full separated boundary cover in decreasing creation order. -/
def arithmeticLastRetainedSeparatedBoundaryDepthReversedCover : (B).toScheme.OpenCover :=
  arithmeticLastRetainedSeparatedBoundaryReversedSmoothCover node data m i j hk hgap hdepth
    (by omega) (arithmeticLastRetainedSeparatedBoundary_stage i j depth hupper) hgen

end FLT.Mazur.WeierstrassDividedDepth
