/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adding redundant coordinates to square presentations

When a subfamily of coordinates presents an algebra with one relation per
coordinate, adjoining any redundant coordinates preserves that count.
-/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k A ι κ : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The zero coordinate family in an augmented algebra has the variables
as its entire relation ideal. -/
theorem ker_aeval_zero_of_augmentation (ε : A →ₐ[k] k) :
    RingHom.ker (aeval (R := k) (fun _ : ι ↦ (0 : A))) =
      Ideal.span (Set.range (X (R := k) (σ := ι))) := by
  let J := Ideal.span (Set.range (X (R := k) (σ := ι)))
  have hmem (f : MvPolynomial ι k) : f - C (constantCoeff f) ∈ J := by
    induction f using MvPolynomial.induction_on with
    | C c => simp
    | add f g hf hg =>
      simpa only [map_add, add_sub_add_comm] using J.add_mem hf hg
    | mul_X f i hf =>
      simpa only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero] using
        J.mul_mem_left f (Ideal.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · intro f hf
    have hh := congrArg ε (show aeval (fun _ : ι ↦ (0 : A)) f = 0 from hf)
    rw [aeval_zero', ε.commutes, map_zero] at hh
    change constantCoeff f = 0 at hh
    simpa only [hh, map_zero, sub_zero] using hmem f
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact aeval_X _ _

/-- A square presentation on a generating subfamily extends to a square
presentation on the original coordinate family. -/
theorem exists_ker_eq_span_of_injective_coordinates (x : ι → A)
    (a : κ → ι) (ha : Function.Injective a)
    (hs : Function.Surjective (aeval (R := k) (x ∘ a)))
    (r : κ → MvPolynomial κ k)
    (hr : RingHom.ker (aeval (R := k) (x ∘ a)) = Ideal.span (Set.range r)) :
    ∃ g : ι → MvPolynomial ι k,
      RingHom.ker (aeval (R := k) x) = Ideal.span (Set.range g) := by
  classical
  choose h hh using fun i ↦ hs (x i)
  let g (i : ι) : MvPolynomial ι k :=
    if hi : ∃ j, a j = i then rename a (r hi.choose) else X i - rename a (h i)
  have hga (j : κ) : g (a j) = rename a (r j) := by
    dsimp only [g]
    rw [dite_eq_left ⟨j, rfl⟩]
    congr 2
    exact ha (Classical.choose_spec (show ∃ t, a t = a j from ⟨j, rfl⟩))
  let J := Ideal.span (Set.range g)
  have hJ : J ≤ RingHom.ker (aeval (R := k) x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x (g i) = 0
    dsimp only [g]
    split_ifs with hi
    · rw [aeval_rename]
      have hm : r hi.choose ∈ RingHom.ker (aeval (R := k) (x ∘ a)) := by
        rw [hr]
        exact Ideal.subset_span ⟨hi.choose, rfl⟩
      exact hm
    · rw [map_sub, aeval_X, aeval_rename, hh, sub_self]
  let q := Ideal.Quotient.mkₐ k J
  have ht : RingHom.ker (aeval (R := k) (x ∘ a)) ≤
      RingHom.ker (q.comp (rename a)) := by
    rw [hr]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change q (rename a (r j)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hga]
    exact Ideal.subset_span ⟨a j, rfl⟩
  let α := (aeval (R := k) (x ∘ a)).liftOfSurjective hs (q.comp (rename a)) ht
  have hα (f : MvPolynomial κ k) : α (aeval (x ∘ a) f) = q (rename a f) :=
    AlgHom.liftOfSurjective_apply _ hs _ ht f
  have hαx (i : ι) : α (x i) = q (X i) := by
    by_cases hi : ∃ j, a j = i
    · obtain ⟨j, rfl⟩ := hi
      simpa only [aeval_X, Function.comp_apply, rename_X] using hα (X j)
    · have he : q (X i - rename a (h i)) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        have hgi : g i = X i - rename a (h i) := by
          dsimp only [g]
          rw [dite_eq_right hi]
        rw [← hgi]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [map_sub, sub_eq_zero] at he
      rw [← hh i, hα]
      exact he.symm
  have hcomp : α.comp (aeval (R := k) x) = q := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X] using hαx i
  refine ⟨g, le_antisymm ?_ hJ⟩
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q f = 0
  rw [← hcomp, AlgHom.comp_apply, show aeval x f = 0 from hf, map_zero]

end MvPolynomial
