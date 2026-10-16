/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclic labels for the two retained arms

With k retained nodes on each arm, the two initial nodes and the terminal
node give 2k+3 labels. The first arm runs down to label zero; the opposite
arm runs up to zero around the cyclic boundary.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- The intended cyclic label of each original retained node. -/
def retainedPolygonIndex (k : ℕ) (a : Fin k) (opposite : Bool) : Fin (2 * k + 3) :=
  if opposite then ⟨k + 3 + a.val, by omega⟩ else ⟨k - a.val, by omega⟩

/-- Every retained node keeps its depth and branch as a distinct cyclic label. -/
theorem retainedPolygonIndex_injective (k : ℕ) :
    Function.Injective (fun ab : Fin k × Bool => retainedPolygonIndex k ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hv := congrArg Fin.val h
  cases b <;> cases d <;> simp only [retainedPolygonIndex, Bool.false_eq_true,
    ↓reduceIte] at hv
  all_goals first | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

/-- The first arm follows the predecessor direction of the actual polygon gluing. -/
theorem retainedPolygonIndex_false_preceding (k a : ℕ) (ha : a + 1 < k) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k ⟨a, by omega⟩ false) =
      retainedPolygonIndex k ⟨a + 1, ha⟩ false := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  unfold retainedPolygonIndex
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [finRotate_of_lt (by omega)]
  apply Fin.ext
  simp only
  omega

/-- The opposite arm follows the successor direction before reversing its coordinates. -/
theorem retainedPolygonIndex_true_preceding (k a : ℕ) (ha : a + 1 < k) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k ⟨a + 1, ha⟩ true) =
      retainedPolygonIndex k ⟨a, by omega⟩ true := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  unfold retainedPolygonIndex
  simp only [↓reduceIte]
  rw [finRotate_of_lt (by omega)]
  rfl

/-- The last node on the first arm attaches to terminal label zero. -/
theorem retainedPolygonIndex_false_terminal (j : ℕ) :
    (finRotate (2 * (j + 1) + 3)).symm
      (retainedPolygonIndex (j + 1) ⟨j, by omega⟩ false) = 0 := by
  apply (Equiv.symm_apply_eq _).mpr
  simp [retainedPolygonIndex]

/-- The last opposite node precedes terminal label zero across the cyclic boundary. -/
theorem retainedPolygonIndex_true_terminal (j : ℕ) :
    (finRotate (2 * (j + 1) + 3)).symm 0 =
      retainedPolygonIndex (j + 1) ⟨j, by omega⟩ true := by
  apply (Equiv.symm_apply_eq _).mpr
  symm
  have he : retainedPolygonIndex (j + 1) ⟨j, by omega⟩ true =
      (⟨2 * (j + 1) + 2, by omega⟩ : Fin (2 * (j + 1) + 3)) := by
    apply Fin.ext
    simp only [retainedPolygonIndex, ↓reduceIte]
    omega
  rw [he]
  exact finRotate_last'

end FLT.Mazur.WeierstrassDividedDepth
