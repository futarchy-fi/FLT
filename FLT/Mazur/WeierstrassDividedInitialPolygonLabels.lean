/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedPolygonLabels

/-!
# Original initial labels and their retained endpoints

The two initial nodes occupy the two labels between the retained arms.
Their cyclic adjacency is proved with the original depth and Boolean labels.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- The two initial nodes lie between the retained arms in the complete polygon. -/
def initialPolygonIndex (k : ℕ) (opposite : Bool) : Fin (2 * k + 3) :=
  if opposite then ⟨k + 2, by omega⟩ else ⟨k + 1, by omega⟩

/-- Each original initial branch has its own polygon label. -/
theorem initialPolygonIndex_injective (k : ℕ) : Function.Injective (initialPolygonIndex k) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a <;> cases b <;> simp only [initialPolygonIndex, Bool.false_eq_true, ↓reduceIte] at hv
  all_goals first | rfl | omega

/-- The opposite initial node immediately follows the first initial node. -/
theorem initialPolygonIndex_preceding (k : ℕ) :
    (finRotate (2 * k + 3)).symm (initialPolygonIndex k true) =
      initialPolygonIndex k false := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  unfold initialPolygonIndex
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [finRotate_of_lt (by omega)]

/-- The first initial node meets the original first retained small branch. -/
theorem initialPolygonIndex_false_retained (k : ℕ) (hk : 0 < k) :
    (finRotate (2 * k + 3)).symm (initialPolygonIndex k false) =
      retainedPolygonIndex k ⟨0, hk⟩ false := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  unfold initialPolygonIndex retainedPolygonIndex
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
  rw [finRotate_of_lt (by omega)]

/-- The original first retained opposite branch meets the opposite initial node. -/
theorem initialPolygonIndex_true_retained (k : ℕ) (hk : 0 < k) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k ⟨0, hk⟩ true) =
      initialPolygonIndex k true := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  unfold initialPolygonIndex retainedPolygonIndex
  simp only [↓reduceIte, Nat.add_zero]
  rw [finRotate_of_lt (by omega)]

/-- Initial labels never overwrite terminal label zero. -/
theorem initialPolygonIndex_ne_terminal (k : ℕ) (b : Bool) : initialPolygonIndex k b ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  cases b <;>
    simp only [initialPolygonIndex, Bool.false_eq_true, ↓reduceIte, Fin.val_zero] at hv <;> omega

/-- Initial labels are distinct from every original retained label. -/
theorem initialPolygonIndex_ne_retained (k : ℕ) (a : Fin k) (b c : Bool) :
    initialPolygonIndex k b ≠ retainedPolygonIndex k a c := by
  intro h
  have hv := congrArg Fin.val h
  cases b <;> cases c <;>
    simp only [initialPolygonIndex, retainedPolygonIndex, Bool.false_eq_true, ↓reduceIte] at hv <;>
      omega

end FLT.Mazur.WeierstrassDividedDepth
