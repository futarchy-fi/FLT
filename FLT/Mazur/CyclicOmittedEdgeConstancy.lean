/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingRotation

/-!
# Removing one edge from the cyclic equality relations

Equalities along every edge except the edge entering one chosen vertex still
force all vertex values to agree. This applies to actual node morphisms when
all normalization components except the chosen one are contracted.
-/

@[expose] public section
namespace FLT.Mazur.PolygonPinching
variable {n : ℕ} [NeZero n] (hn : 0 < n) {A : Sort*}

/-- A cycle with one omitted equality edge still has constant vertex values. -/
theorem eq_of_omitted_edge (v : Fin n → A) (i : Fin n)
    (hv : ∀ j, next hn j ≠ i → v (next hn j) = v j) (j : Fin n) : v j = v i := by
  have step : ∀ (k : ℕ) (hk : k < n), v (i + ⟨k, hk⟩) = v i := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have he : next hn (i + ⟨k, hk'⟩) = i + ⟨k + 1, hk⟩ := by
        rw [next_eq_add_one, add_assoc]
        congr 1
        apply Fin.ext
        simp only [Fin.val_add]
        change (k + 1 % n) % n = k + 1
        rw [Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt hk
      have hne : i + (⟨k + 1, hk⟩ : Fin n) ≠ i := by
        intro H
        have H' : (⟨k + 1, hk⟩ : Fin n) = 0 := add_left_cancel (H.trans (add_zero i).symm)
        have := congrArg Fin.val H'
        simp only [Fin.val_zero] at this
        omega
      have H := hv (i + ⟨k, hk'⟩) (he ▸ hne)
      rw [he] at H
      exact H.trans (ih hk')
  have H := step (j - i).val (j - i).isLt
  simpa only [Fin.eta, add_sub_cancel] using H

end FLT.Mazur.PolygonPinching
