/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentSource

/-!
# The target coordinates are the next retained source coordinates

The identity concerns the full arithmetic chart, before selecting an incidence
open or discarding nilpotents. It allows successive coverage results to compose.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)

/-- Recovering the adjacent target is exactly recovering the next retained source. -/
theorem arithmeticFixedAdjacentTargetCoordinates_eq_next_source :
    arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi =
      arithmeticFixedAdjacentSourceCoordinates hπ data m k hk (i + 1) hiNext := rfl

end FLT.Mazur.WeierstrassDividedDepth
