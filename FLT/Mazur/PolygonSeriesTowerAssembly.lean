/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundarySeriesDegree

/-!
# Assembling adjacent-compatible homogeneous sections

Compatibility with adjacent maps implies compatibility with every original
stage map. Assembly lands in the specified homogeneous submodule and retains
all evaluations and complete-base scalar actions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (d : ℕ)

/-- Adjacent compatibility of actual homogeneous sections retains every original stage map. -/
theorem boundarySeriesDegree_compatible_all
    (s : ∀ a, boundarySeriesDegree R n h a d)
    (hs : ∀ a, boundarySeriesDegreeTransition R n h a d (s (a + 1)) = s a)
    {a b : ℕ} (f : a ⟶ b) : boundarySectionsMap R n h f (s b).val = (s a).val := by
  have hab := leOfHom f
  induction hab with
  | refl =>
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    rw [hf, boundarySectionsMap_id]
    rfl
  | @step b hab ih =>
    have hf : f = homOfLE hab ≫ homOfLE (Nat.le_succ b) := Subsingleton.elim _ _
    rw [hf, boundarySectionsMap_comp]
    change boundarySectionsMap R n h (homOfLE hab)
      (boundarySectionsMap R n h (homOfLE (Nat.le_succ b)) (s (b + 1)).val) = _
    rw [show boundarySectionsMap R n h (homOfLE (Nat.le_succ b)) (s (b + 1)).val =
      (s b).val from congrArg Subtype.val (hs b)]
    exact ih (homOfLE hab)

/-- Assemble the actual homogeneous tower without changing any stage projection. -/
def compatibleDegreeOfAdjacent (s : ∀ a, boundarySeriesDegree R n h a d)
    (hs : ∀ a, boundarySeriesDegreeTransition R n h a d (s (a + 1)) = s a) :
    compatibleSectionDegree R n h d :=
  ⟨compatibleOfStages R n h (fun a ↦ (s a).val)
    (boundarySeriesDegree_compatible_all R n h d s hs), by
      intro a
      rw [compatibleEval_ofStages]
      exact (s a).property⟩

/-- Assembly evaluates to the original homogeneous section at each stage. -/
theorem compatibleDegreeOfAdjacent_eval (s : ∀ a, boundarySeriesDegree R n h a d)
    (hs : ∀ a, boundarySeriesDegreeTransition R n h a d (s (a + 1)) = s a) (m : ℕ) :
    compatibleEval R n h m (compatibleDegreeOfAdjacent R n h d s hs).val = (s m).val :=
  compatibleEval_ofStages R n h _ (boundarySeriesDegree_compatible_all R n h d s hs) m

/-- Homogeneous evaluation commutes with the original complete-base scalar action. -/
theorem compatibleDegree_eval_smul (m : ℕ) (r : PowerSeries R)
    (s : compatibleSectionDegree R n h d) :
    compatibleEval R n h m (r • s).val =
      boundarySeriesScalars R n h m r * compatibleEval R n h m s.val := by
  change compatibleEval R n h m (r • s.val) = _
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap]

end FLT.Mazur.PolygonInfinitesimalStages
