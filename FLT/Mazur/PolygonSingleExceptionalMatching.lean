/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonIncidence

/-!
# Propagation around a polygon with one exceptional component

If the two endpoint scalars agree on every unmarked component, node matching
forces agreement on the marked component too. All endpoint scalars then have
one common value. The proof uses the vanishing total cyclic difference and
works for every positive polygon size, including one.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSingleExceptionalMatching

open PolygonPinching PolygonIncidence

variable {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (j : Fin n)
  (u v : Fin n → K)

/-- One exceptional endpoint discrepancy vanishes whenever all nodes match. -/
theorem exceptional_eq (hoff : ∀ i, i ≠ j → u i = v i)
    (hedge : ∀ i, u i = v (next hn i)) : u j = v j := by
  have hd : ∀ i, difference K hn v i = v i - u i := by
    intro i
    rw [difference_apply, ← hedge i]
  have hs : (∑ i, (v i - u i)) = 0 := by
    simpa only [total_apply, hd] using total_difference K hn v
  have hj : (∑ i, (v i - u i)) = v j - u j := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      rw [hoff i hij, sub_self]
    · simp
  rw [hj] at hs
  exact (sub_eq_zero.mp hs).symm

/-- Every matched endpoint is the scalar at the marked component. -/
theorem all_eq (hoff : ∀ i, i ≠ j → u i = v i)
    (hedge : ∀ i, u i = v (next hn i)) (i : Fin n) :
    u i = v j ∧ v i = v j := by
  have huv (k : Fin n) : u k = v k := by
    by_cases hk : k = j
    · subst k
      exact exceptional_eq hn j u v hoff hedge
    · exact hoff k hk
  have hz : difference K hn v = 0 := by
    funext k
    exact sub_eq_zero.mpr ((huv k).symm.trans (hedge k))
  have hc := (eq_initial_of_difference_eq_zero hn v hz i).trans
    (eq_initial_of_difference_eq_zero hn v hz j).symm
  exact ⟨(huv i).trans hc, hc⟩

/-- The complete node equations are equivalent to one common endpoint scalar. -/
theorem matching_iff (hoff : ∀ i, i ≠ j → u i = v i) :
    (∀ i, u i = v (next hn i)) ↔ ∃ c : K, (∀ i, u i = c) ∧ ∀ i, v i = c := by
  constructor
  · intro hedge
    exact ⟨v j, fun i ↦ (all_eq hn j u v hoff hedge i).1,
      fun i ↦ (all_eq hn j u v hoff hedge i).2⟩
  · rintro ⟨c, hu, hv⟩ i
    exact (hu i).trans (hv (next hn i)).symm

end FLT.Mazur.PolygonSingleExceptionalMatching
