/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Extending the Odlyzko base case to every degree

This is endgame node S2.  The analytic work supplies a monotone lower-bound function and
the certified degree-18 value; this file contains only the order-theoretic propagation.
-/

@[expose] public section

namespace Odlyzko

/-- A nondecreasing lower bound which reaches `log 8.25` at degree `18` reaches it at
every larger degree.  The base case is an explicit hypothesis because its numerical
certificate is the separate endgame node R6. -/
theorem uniformBound_of_monotone (lowerBound : ℕ → ℝ)
    (hmono : Monotone lowerBound)
    (h18 : Real.log 8.25 ≤ lowerBound 18) :
    ∀ n, 18 ≤ n → Real.log 8.25 ≤ lowerBound n := by
  intro n hn
  exact h18.trans (hmono hn)

end Odlyzko
