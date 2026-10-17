/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSplitParameter
public import FLT.Mazur.PolygonCompleteBoundaryCartesian
public import FLT.Mazur.PolygonCompleteParameterTranslation

/-!
# Arbitrary closed smooth parameters and the unmoved whole-polygon comparison

A section over any residue-field scheme defines a point of the actual complete
smooth group. The unchanged whole polygon identifies with the original complete
base change before applying any translation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "G" => PolygonSplitGroup.model K n
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "B" => Over.mk (g ≫ completeClosedBase K)
local notation "CX" => Functor.obj (Over.pullback g) (C)

/-- Every varying original smooth section is an actual point of the complete smooth group. -/
def completeClosedParameterSection
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (PolygonSplitGroup.model K n)) : (B) ⟶ (M) :=
  Over.homMk (c.left ≫ pullback.fst (G).hom g ≫ completeClosedSplitInclusion K n h) (by
    have hc : c.left ≫ pullback.snd (G).hom g = 𝟙 T := c.w
    rw [Category.assoc, Category.assoc, completeClosedSplitInclusion_base,
      ← Category.assoc (pullback.fst _ _) _ _, pullback.condition, Category.assoc,
      ← Category.assoc c.left _ _, hc]
    exact Category.id_comp _)

/-- The varying point retains its original full split parameter before closed inclusion. -/
theorem completeClosedParameterSection_left
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (PolygonSplitGroup.model K n)) :
    (completeClosedParameterSection K n h g c).left =
      c.left ≫ pullback.fst (G).hom g ≫ completeClosedSplitInclusion K n h := rfl

/-- The unmoved closed polygon is the entire original complete product over the new base. -/
def completeUnmovedBoundaryProductIso : (CX).left ≅ ((X) ⊗ (B)).left :=
  (completeBoundaryParameter_isPullback K n h g).isoPullback

/-- The unmoved comparison preserves the original complete-family inclusion. -/
@[reassoc] theorem completeUnmovedBoundaryProductIso_fst :
    (completeUnmovedBoundaryProductIso K n h g).hom ≫ (fst (X) (B)).left =
      completeBoundaryParameterMap K n h g :=
  (completeBoundaryParameter_isPullback K n h g).isoPullback_hom_fst

/-- The unmoved comparison preserves the actual parameter scheme projection. -/
@[reassoc] theorem completeUnmovedBoundaryProductIso_snd :
    (completeUnmovedBoundaryProductIso K n h g).hom ≫ (snd (X) (B)).left = (CX).hom :=
  (completeBoundaryParameter_isPullback K n h g).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
