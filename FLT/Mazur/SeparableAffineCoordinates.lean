/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Separable residue coordinates avoid arbitrary polynomial zero loci

Even when the coefficients lie in a larger geometric field, a nonzero
polynomial does not vanish at every tuple separable over the base field.
This supplies the polynomial avoidance step for geometric open coverage.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SeparableAffineCoordinates
variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- A separably closed field is infinite, including in positive characteristic. -/
theorem infinite_of_isSepClosed [IsSepClosed k] : Infinite k := by
  cases finite_or_infinite k with
  | inl h =>
    let _ := h
    let _ : IsAlgClosed k := IsSepClosed.isAlgClosed_of_perfectField k
    infer_instance
  | inr h => exact h

/-- A nonzero polynomial over an extension does not vanish on an infinite subfield grid. -/
theorem exists_eval_ne_zero [Infinite k] {σ : Type} (p : MvPolynomial σ K) (hp : p ≠ 0) :
    ∃ v : σ → k, MvPolynomial.eval (fun i ↦ algebraMap k K (v i)) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ ↦ Set.range (algebraMap k K))
    (fun _ ↦ Set.infinite_range_of_injective (algebraMap k K).injective)
  intro x hx
  choose v hv using fun i ↦ hx i (Set.mem_univ i)
  have he : x = fun i ↦ algebraMap k K (v i) := funext (fun i ↦ (hv i).symm)
  rw [he, h, map_zero]

/-- Separable coordinates avoid any nonzero polynomial with coefficients in a geometric field. -/
theorem exists_separable_eval_ne_zero [IsSepClosed K] {σ : Type}
    (p : MvPolynomial σ K) (hp : p ≠ 0) :
    ∃ v : σ → K, (∀ i, IsSeparable k (v i)) ∧ MvPolynomial.eval v p ≠ 0 := by
  let _ : IsSepClosed (separableClosure k K) := IsSepClosure.sep_closed k
  let _ : Infinite (separableClosure k K) := infinite_of_isSepClosed
  obtain ⟨v, hv⟩ := exists_eval_ne_zero (k := separableClosure k K) p hp
  exact ⟨fun i ↦ (v i).1, fun i ↦ (v i).2, hv⟩

end FLT.Mazur.SeparableAffineCoordinates
