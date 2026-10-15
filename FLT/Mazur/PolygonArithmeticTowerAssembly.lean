/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIntegralDegree

/-!
# Assembling adjacent-compatible homogeneous sections

Compatibility with adjacent maps implies compatibility with every original
stage map. Assembly lands in the specified homogeneous submodule and retains
all evaluations and integral-base scalar actions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n) (d : ℕ)

/-- Adjacent compatibility of actual homogeneous sections retains every original stage map. -/
theorem boundaryIntegralDegree_compatible_all
    (s : ∀ a, boundaryIntegralDegree A π n h a d)
    (hs : ∀ a, boundaryIntegralDegreeTransition A π n h a d (s (a + 1)) = s a)
    {a b : ℕ} (f : a ⟶ b) : boundarySectionsMap A π n h f (s b).val = (s a).val := by
  have hab := leOfHom f
  induction hab with
  | refl =>
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    rw [hf, boundarySectionsMap_id]
    rfl
  | @step b hab ih =>
    have hf : f = homOfLE hab ≫ homOfLE (Nat.le_succ b) := Subsingleton.elim _ _
    rw [hf, boundarySectionsMap_comp]
    change boundarySectionsMap A π n h (homOfLE hab)
      (boundarySectionsMap A π n h (homOfLE (Nat.le_succ b)) (s (b + 1)).val) = _
    rw [show boundarySectionsMap A π n h (homOfLE (Nat.le_succ b)) (s (b + 1)).val =
      (s b).val from congrArg Subtype.val (hs b)]
    exact ih (homOfLE hab)

/-- Assemble the actual homogeneous tower without changing any stage projection. -/
def compatibleDegreeOfAdjacent (s : ∀ a, boundaryIntegralDegree A π n h a d)
    (hs : ∀ a, boundaryIntegralDegreeTransition A π n h a d (s (a + 1)) = s a) :
    compatibleSectionDegree A π n h d :=
  ⟨compatibleOfStages A π n h (fun a ↦ (s a).val)
    (boundaryIntegralDegree_compatible_all A π n h d s hs), by
      intro a
      rw [compatibleEval_ofStages]
      exact (s a).property⟩

/-- Assembly evaluates to the original homogeneous section at each stage. -/
theorem compatibleDegreeOfAdjacent_eval (s : ∀ a, boundaryIntegralDegree A π n h a d)
    (hs : ∀ a, boundaryIntegralDegreeTransition A π n h a d (s (a + 1)) = s a) (m : ℕ) :
    compatibleEval A π n h m (compatibleDegreeOfAdjacent A π n h d s hs).val = (s m).val :=
  compatibleEval_ofStages A π n h _ (boundaryIntegralDegree_compatible_all A π n h d s hs) m

/-- Homogeneous evaluation commutes with the original integral-base scalar action. -/
theorem compatibleDegree_eval_smul (m : ℕ) (r : A)
    (s : compatibleSectionDegree A π n h d) :
    compatibleEval A π n h m (r • s).val =
      boundaryIntegralScalars A π n h m r * compatibleEval A π n h m s.val := by
  change compatibleEval A π n h m (r • s.val) = _
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap]

end FLT.Mazur.PolygonArithmeticStages
