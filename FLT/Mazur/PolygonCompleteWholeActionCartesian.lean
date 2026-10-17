/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeShear

/-!
# The original full action square is Cartesian

The universal shear identifies the action with the second projection while
retaining the actual smooth parameter. Thus the original action is a base change
of the original whole-family structure morphism, including at singular inputs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h

/-- The original universal shear is Cartesian over its unchanged smooth parameter. -/
theorem completeWholeShear_isPullback :
    IsPullback (completeWholeShearHom K n h).left
      (fst (M) (X)).left (fst (M) (X)).left (𝟙 (M).left) := by
  let _ : IsIso (completeWholeShearHom K n h).left :=
    ((Over.forget _).mapIso (completeWholeShearIso K n h)).isIso_hom
  apply IsPullback.of_horiz_isIso
  constructor
  simpa only [Category.comp_id, Over.comp_left] using
    congrArg Over.Hom.left (completeWholeShearHom_fst K n h)

/-- The full original action and its smooth parameter form a Cartesian square. -/
theorem completeWholeAction_isPullback :
    IsPullback (completeWholeAction K n h).left (fst (M) (X)).left (X).hom (M).hom := by
  have hs := (completeWholeShear_isPullback K n h).paste_horiz
    (IsPullback.of_hasPullback (M).hom (X).hom).flip
  have he := congrArg Over.Hom.left (completeWholeShearHom_snd K n h)
  change (completeWholeShearHom K n h).left ≫ pullback.snd (M).hom (X).hom =
    (completeWholeAction K n h).left at he
  simpa only [he, Category.id_comp] using hs

end FLT.Mazur.PolygonInfinitesimalStages
