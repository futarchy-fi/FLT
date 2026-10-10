/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFreeDualProjectiveAtlas

/-!
# The actual chart points of a dual projective atlas section

Cartesian atlas squares lift a global section to genuine local projective
points. Their restriction squares are proved from the original section;
no local point compatibility is supplied as extra data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionChartPoints
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ space M hM) (hs : s ≫ projection M hM = 𝟙 X)

/-- Lift the original section to an actual finite free projective chart. -/
def point (i : Index M) :
    i.val.toScheme ⟶ ProjectiveSpace.space Γ(i.val.toScheme, ⊤) (coordinates M i) :=
  (chart_isPullback M hM i).lift (𝟙 _) (i.val.ι ≫ s) (by
    rw [Category.id_comp, Category.assoc, hs, Category.comp_id])

/-- The lifted point is a section over the original affine base chart. -/
@[reassoc]
lemma point_projection (i : Index M) :
    point M hM s hs i ≫ ProjectiveSpace.affineProjection i.val.toScheme (coordinates M i) =
      𝟙 i.val.toScheme := (chart_isPullback M hM i).lift_fst _ _ _

/-- The local point recovers the given global section in the actual glued atlas. -/
@[reassoc]
lemma point_chartMap (i : Index M) :
    point M hM s hs i ≫ chartMap M hM i = i.val.ι ≫ s :=
  (chart_isPullback M hM i).lift_snd _ _ _

/-- The genuine dual chart inclusion gives the local section's restriction square. -/
lemma point_refinement {i j : Index M} (h : i ≤ j) :
    X.homOfLE h ≫ point M hM s hs j =
      point M hM s hs i ≫
        FiniteFreeChartTransitions.dualChartInclusion M h (chart M i) (chart M j) := by
  apply (cancel_mono (chartMap M hM j)).mp
  rw [Category.assoc, point_chartMap, ← Category.assoc, X.homOfLE_ι, Category.assoc]
  have hw : FiniteFreeChartTransitions.dualChartInclusion M h (chart M i) (chart M j) ≫
      chartMap M hM j = chartMap M hM i :=
    colimit.w (gluingData M hM).functor (homOfLE h)
  rw [hw, point_chartMap]

end FLT.Mazur.DualAtlasSectionChartPoints
