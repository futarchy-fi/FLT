/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCompletedPoints

/-! # Every original positive-precision point extends to a completed point -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Formal smoothness gives an actual compatible lift of any prescribed residue point.
The finite-level indices may grow with precision; no uniform finite stage is assumed. -/
theorem rationalPlaceCompletedPointEval_surjective (n : ℕ) :
    Function.Surjective (X.rationalPlaceCompletedPointEval n) := by
  intro a
  let P (s : ℕ) := X.PointColimit (ComplexIntegerModPow p (s + 1))
  let q {s t : ℕ} (h : s ≤ t) : P t → P s :=
    X.pointColimitMap (rationalPlaceIntegerModPowReduce p (Nat.add_le_add_right h 1))
  have qid (s : ℕ) (x : P s) : q (le_refl s) x = x := by
    dsimp [q]
    rw [rationalPlaceIntegerModPowReduce_refl, X.pointColimitMap_id]
  have qcomp {s t u : ℕ} (h : s ≤ t) (k : t ≤ u) (x : P u) :
      q h (q k x) = q (h.trans k) x := by
    dsimp [q]
    rw [← X.pointColimitMap_comp, rationalPlaceIntegerModPowReduce_comp]
  let F (k : ℕ) := {x : P (n + k) // q (Nat.le_add_right n k) x = a}
  have lift (k : ℕ) (x : F k) : ∃ y : F (k + 1),
      q (Nat.add_le_add_left (Nat.le_succ k) n) y.val = x.val := by
    obtain ⟨y, hy⟩ := rationalPlacePointPrecision_surjective X
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_succ k) n) 1)
      (Nat.zero_lt_succ _) x.val
    have hy' : q (Nat.add_le_add_left (Nat.le_succ k) n) y = x.val := hy
    refine ⟨⟨y, ?_⟩, hy'⟩
    rw [← qcomp (Nat.le_add_right n k) (Nat.add_le_add_left (Nat.le_succ k) n), hy']
    exact x.property
  let f : ∀ k, F k := fun k ↦ Nat.rec
    (motive := F) ⟨a, qid n a⟩ (fun k x ↦ (lift k x).choose) k
  have hf (k : ℕ) :
      q (Nat.add_le_add_left (Nat.le_succ k) n) (f (k + 1)).val = (f k).val :=
    (lift k (f k)).choose_spec
  let x (s : ℕ) : P s := q (Nat.le_add_left s n) (f s).val
  have hx (s : ℕ) : q (Nat.le_succ s) (x (s + 1)) = x s := by
    dsimp [x]
    rw [qcomp, ← hf s, qcomp] <;> omega
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (f n).property

/-- Every finite original point over O_C/p^(s+1) occurs in the completed group. -/
theorem exists_completedPoint_of_level (n s : ℕ)
    (a : (X.level n).CoordinateRing →ₐ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      ComplexIntegerModPow p (s + 1)) :
    ∃ x : X.RationalPlaceCompletedPoints,
      X.rationalPlaceCompletedPointEval s x = X.pointColimitMk n a :=
  X.rationalPlaceCompletedPointEval_surjective s _

end ThreeAdicPlan.PDivisibleSystem
