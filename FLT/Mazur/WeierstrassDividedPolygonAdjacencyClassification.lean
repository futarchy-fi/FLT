/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonLabels

/-!
# Exact adjacency classification for the original polygon labels

Only the first retained node meets an initial label, and only consecutive
nodes on the same retained arm are adjacent. These statements retain both
Boolean labels and the original depths.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- No retained node occupies the terminal polygon label. -/
theorem retainedPolygonIndex_ne_zero (k : ℕ) (a : Fin k) (b : Bool) :
    retainedPolygonIndex k a b ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  cases b <;> simp only [retainedPolygonIndex, Bool.false_eq_true, ↓reduceIte,
    Fin.val_zero] at hv <;> omega

/-- Away from zero, predecessor equality is precisely ordinary integer adjacency. -/
theorem polygonPredecessor_eq_iff (k : ℕ) (i j : Fin (2 * k + 3)) (hi : i ≠ 0) :
    (finRotate (2 * k + 3)).symm i = j ↔ i.val = j.val + 1 := by
  let _ : NeZero (2 * k + 3) := ⟨by omega⟩
  rw [Fin.ext_iff, coe_finRotate_symm_of_ne_zero hi]
  have hpos : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
  omega

/-- The predecessor side of an initial node meets exactly the first small retained node. -/
theorem initialPolygonIndex_preceding_retained_iff (k : ℕ) (a : Fin k) (b c : Bool) :
    (finRotate (2 * k + 3)).symm (initialPolygonIndex k b) = retainedPolygonIndex k a c ↔
      b = false ∧ c = false ∧ a.val = 0 := by
  rw [polygonPredecessor_eq_iff k _ _ (initialPolygonIndex_ne_terminal k b)]
  cases b <;> cases c <;> simp [initialPolygonIndex, retainedPolygonIndex] <;> omega

/-- The successor side of an initial node meets exactly the first opposite retained node. -/
theorem retainedPolygonIndex_preceding_initial_iff (k : ℕ) (a : Fin k) (b c : Bool) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k a c) = initialPolygonIndex k b ↔
      b = true ∧ c = true ∧ a.val = 0 := by
  rw [polygonPredecessor_eq_iff k _ _ (retainedPolygonIndex_ne_zero k a c)]
  cases b <;> cases c <;> simp [initialPolygonIndex, retainedPolygonIndex] <;> omega

/-- Retained adjacency is exactly consecutive depth on one original arm. -/
theorem retainedPolygonIndex_preceding_iff (k : ℕ) (a d : Fin k) (b c : Bool) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k a b) =
        retainedPolygonIndex k d c ↔
      (b = false ∧ c = false ∧ a.val + 1 = d.val) ∨
        (b = true ∧ c = true ∧ d.val + 1 = a.val) := by
  rw [polygonPredecessor_eq_iff k _ _ (retainedPolygonIndex_ne_zero k a b)]
  cases b <;> cases c <;> simp [retainedPolygonIndex] <;> omega

/-- At positive retention depth no initial node immediately follows the terminal node. -/
theorem initialPolygonIndex_preceding_ne_zero (k : ℕ) (hk : 0 < k) (b : Bool) :
    (finRotate (2 * k + 3)).symm (initialPolygonIndex k b) ≠ 0 := by
  intro h
  have hv := (polygonPredecessor_eq_iff k _ _ (initialPolygonIndex_ne_terminal k b)).mp h
  cases b <;> simp only [initialPolygonIndex, Bool.false_eq_true, ↓reduceIte,
    Fin.val_mk, Fin.val_zero] at hv <;> omega

/-- At positive retention depth no initial node immediately precedes terminal label zero. -/
theorem zero_preceding_ne_initialPolygonIndex (k : ℕ) (hk : 0 < k) (b : Bool) :
    (finRotate (2 * k + 3)).symm 0 ≠ initialPolygonIndex k b := by
  have he : (finRotate (2 * k + 3)).symm 0 = ⟨2 * k + 2, by omega⟩ :=
    (Equiv.symm_apply_eq _).mpr finRotate_last'.symm
  rw [he]
  intro h
  have hv := congrArg Fin.val h
  cases b <;> simp only [initialPolygonIndex, Bool.false_eq_true, ↓reduceIte] at hv <;> omega

end FLT.Mazur.WeierstrassDividedDepth
