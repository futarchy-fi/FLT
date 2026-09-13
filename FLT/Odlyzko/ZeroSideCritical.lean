/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Data.Complex.Basic

/-!
# Zero-side positivity on the critical line

On `s = 1/2 + iγ`, the real zero contribution is the Fourier transform at the real
frequency `γ`.  Thus Fourier nonnegativity gives the easy, on-line half of the zero discard.
-/

@[expose] public section

namespace Odlyzko

/-- The point of height `γ` on the critical line. -/
noncomputable def criticalPoint (γ : ℝ) : ℂ := (1 / 2 : ℝ) + γ * Complex.I

/-- P3: identification with a nonnegative Fourier transform makes the contribution nonnegative. -/
theorem criticalLineContribution_nonneg (phi : ℂ → ℂ) (fourier : ℝ → ℝ) (γ : ℝ)
    (hidentify : (phi (criticalPoint γ)).re = fourier γ)
    (hfourier : ∀ t, 0 ≤ fourier t) :
    (phi (criticalPoint γ)).re = fourier γ ∧ 0 ≤ (phi (criticalPoint γ)).re := by
  exact ⟨hidentify, hidentify.symm ▸ hfourier γ⟩

end Odlyzko
