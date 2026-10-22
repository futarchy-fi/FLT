/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthFeasibility

/-!
# Final-stage indexing at even and odd node depth

Data at stage j is final when the node depth is 2*j or 2*j+1. In particular,
there is no retained chart of creation depth j requiring data at j+1.
This is an indexing exclusion; it supplies no formula or atlas coverage.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth n : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))

include node data in
/-- A supplied odd-terminal stage is exactly the last stage in the data family. -/
theorem dataFamily_odd_final_stage (j : ℕ) (hj : j ≤ n) (hodd : depth = 2 * j + 1) :
    n = j := by
  have h := dataFamily_twice_last_le node data
  omega

include node data in
/-- A supplied middle-terminal stage is exactly the last stage in the data family. -/
theorem dataFamily_even_final_stage (j : ℕ) (hj : j ≤ n) (heven : depth = 2 * j) :
    n = j := by
  have h := dataFamily_twice_last_le node data
  omega

include node data in
/-- Odd node depth excludes the extra data required by a retained chart of creation depth j. -/
theorem dataFamily_odd_no_next (j : ℕ) (hodd : depth = 2 * j + 1) : ¬ j + 1 ≤ n := by
  have h := dataFamily_twice_last_le node data
  omega

include node data in
/-- Every feasible retained creation depth is strictly below the odd-terminal stage. -/
theorem dataFamily_odd_retained_lt (j r : ℕ) (hodd : depth = 2 * j + 1)
    (hr : r + 1 ≤ n) : r < j := by
  have h := dataFamily_twice_last_le node data
  omega

end FLT.Mazur.WeierstrassDividedDepth
