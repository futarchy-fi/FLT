/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingReflectionIndices

/-!
# Arithmetic of reflected component and node positions

Compute the original cyclic reflection in natural-number coordinates. These
formulas distinguish the exchanged terminal components from their fixed common node.
-/

@[expose] public section
namespace FLT.Mazur.PolygonPinching
variable (s : ℕ)

/-- The first chain position goes to the same level of the second chain. -/
theorem reflectIndex_oddFirstChain (j : Fin (s + 2)) :
    reflectIndex (⟨j.val + 1, by omega⟩ : Fin (2 * s + 5)) =
      ⟨2 * s + 4 - j.val, by omega⟩ := by
  apply Fin.ext
  rw [reflectIndex_val _ (by intro h; have := congrArg Fin.val h; simp at this)]
  dsimp only
  omega

/-- The second chain position returns to the same level of the first chain. -/
theorem reflectIndex_oddSecondChain (j : Fin (s + 2)) :
    reflectIndex (⟨2 * s + 4 - j.val, by omega⟩ : Fin (2 * s + 5)) =
      ⟨j.val + 1, by omega⟩ := by
  rw [← reflectIndex_oddFirstChain s j, reflectIndex_reflectIndex]

/-- Reflection exchanges the two terminal components of an odd polygon. -/
theorem reflectIndex_oddTerminal :
    reflectIndex (⟨s + 2, by omega⟩ : Fin (2 * s + 5)) = ⟨s + 3, by omega⟩ := by
  apply Fin.ext
  rw [reflectIndex_val _ (by intro h; have := congrArg Fin.val h; simp at this)]
  dsimp only
  omega

/-- The common terminal node is fixed by odd-polygon reflection. -/
theorem reflectNodeIndex_oddTerminal :
    reflectNodeIndex (⟨s + 2, by omega⟩ : Fin (2 * s + 5)) = ⟨s + 2, by omega⟩ := by
  apply Fin.ext
  rw [reflectNodeIndex_val]
  dsimp only
  omega

/-- First-branch nodes, including both ends, go to second-branch nodes at the same level. -/
theorem reflectNodeIndex_oddFirstChain (j : Fin (s + 2)) :
    reflectNodeIndex (⟨j.val, by omega⟩ : Fin (2 * s + 5)) =
      ⟨2 * s + 4 - j.val, by omega⟩ := by
  apply Fin.ext
  rw [reflectNodeIndex_val]
  dsimp only
  omega

/-- Second-branch nodes return to first-branch nodes without a level shift. -/
theorem reflectNodeIndex_oddSecondChain (j : Fin (s + 2)) :
    reflectNodeIndex (⟨2 * s + 4 - j.val, by omega⟩ : Fin (2 * s + 5)) =
      ⟨j.val, by omega⟩ := by
  rw [← reflectNodeIndex_oddFirstChain s j, reflectNodeIndex_reflectNodeIndex]

end FLT.Mazur.PolygonPinching
