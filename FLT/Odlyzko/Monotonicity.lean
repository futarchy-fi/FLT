/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.ScaledInequality

/-!
# Fixed-scale monotonicity in the field degree

At a fixed positive scale `y`, the Q5 lower bound has the form `L1(y) - C(y) / n`.
For a positive pole correction `C(y)`, this is nondecreasing on the positive natural degrees.
-/

@[expose] public section

namespace Odlyzko

/-- The lower bound from Q5, viewed as a function of the degree. -/
noncomputable def fixedScaleLowerBound (archimedeanIntegral : ℝ → ℂ)
    (phi : ℝ → ℂ → ℂ) (y : ℝ) (n : ℕ) : ℝ :=
  L1 archimedeanIntegral y - poleCorrection phi y / n

/-- S1: at fixed `y`, increasing a positive degree can only improve the Q5 lower bound. -/
theorem fixedScaleLowerBound_mono {archimedeanIntegral : ℝ → ℂ}
    {phi : ℝ → ℂ → ℂ} {y : ℝ} {m n : ℕ}
    (hpole : 0 < poleCorrection phi y) (hm : 1 ≤ m) (hmn : m ≤ n) :
    fixedScaleLowerBound archimedeanIntegral phi y m ≤
      fixedScaleLowerBound archimedeanIntegral phi y n := by
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : poleCorrection phi y / (n : ℝ) ≤ poleCorrection phi y / (m : ℝ) :=
    div_le_div_of_nonneg_left hpole.le hmR hmnR
  unfold fixedScaleLowerBound
  linarith

/-- The same monotonicity packaged on the domain of positive natural degrees. -/
theorem fixedScaleLowerBound_monotoneOn (archimedeanIntegral : ℝ → ℂ)
    (phi : ℝ → ℂ → ℂ) (y : ℝ) (hpole : 0 < poleCorrection phi y) :
    MonotoneOn (fixedScaleLowerBound archimedeanIntegral phi y) (Set.Ici 1) := by
  intro m hm n _hn hmn
  exact fixedScaleLowerBound_mono hpole hm hmn

end Odlyzko
