/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistingSheaf

/-!
# The degree-one transition as a chart section

On every common subopen the transition is the restriction of X_j/X_i from
chart i. This fixes the orientation before pulling back along a section map.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The hyperplane transition is the restriction of the first chart's coordinate. -/
lemma twistCocycle_one_chartSection (i j : ι) (V : (space R ι).Opens)
    (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j) :
    ((twistCocycle R ι 1).unit i j V hi hj : Γ(space R ι, V)) =
      (space R ι).presheaf.map (homOfLE hi).op
        (Proj.awayToSection (grading R ι) (X i) (coordinate R ι i j)) := by
  change (space R ι).presheaf.map _ ((space R ι).presheaf.map _
    (Proj.awayToSection (grading R ι) (X i * X j)
      (transitionUnit R ι 1 i j))) = _
  rw [transitionUnit_one, ratioUnit_val]
  have he := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (grading R ι) (isHomogeneous_X R j) rfl)
    (coordinate R ι i j)
  change Proj.awayToSection (grading R ι) (X i * X j)
    (toOverlap R ι i j (coordinate R ι i j)) = _ at he
  rw [he]
  simp only [← Functor.map_comp_apply]
  rfl

end FLT.Mazur.ProjectiveSpace
