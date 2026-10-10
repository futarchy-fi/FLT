/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteFreeDirectedCover
public import FLT.Mazur.FiniteFreeDualProjectiveRefinement
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Gluing the projective atlas with dual homogeneous generators

For a locally finite free sheaf the contragredient chart transitions glue to an
actual scheme over its base. The projective chart squares are cartesian and
cover the glued scheme. This establishes the dual convention geometrically;
the functor of line subbundles and its Abel-fiber comparison remain separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFreeDualProjectiveAtlas
open FCurve AffineFiniteFreeAtlas
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)

/-- The projective chart functor with dual homogeneous-generator transitions. -/
def diagram : Index M ⥤ Scheme.{u} where
  obj i := ProjectiveSpace.space Γ(i.val.toScheme, ⊤) (coordinates M i)
  map {i j} f := FiniteFreeChartTransitions.dualChartInclusion M f.le (chart M i) (chart M j)
  map_id i := FiniteFreeChartTransitions.dualChartInclusion_self M (chart M i)
  map_comp f g :=
    (FiniteFreeChartTransitions.dualChartInclusion_comp M f.le g.le _ _ _).symm

/-- Local finite freeness supplies the actual gluing datum in the dual convention. -/
def gluingData : (AffineFiniteFreeAtlas.cover M hM).RelativeGluingData where
  functor := diagram M
  natTrans :=
    { app i := ProjectiveSpace.affineProjection i.val.toScheme (coordinates M i)
      naturality := by
        intro i j f
        exact FiniteFreeChartTransitions.dualChartInclusion_projection M f.le
          (chart M i) (chart M j) }
  equifibered := by
    intro i j f
    exact FiniteFreeChartTransitions.dualChartInclusion_isPullback M f.le (chart M i) (chart M j)

/-- The glued projective scheme with generators dual to the sheaf coordinates. -/
def space : Scheme.{u} := (gluingData M hM).glued

/-- Its projection targets the original base scheme. -/
def projection : space M hM ⟶ X := (gluingData M hM).toBase

/-- The inclusion of one actual affine projective chart into the glued scheme. -/
def chartMap (i : Index M) :
    ProjectiveSpace.space Γ(i.val.toScheme, ⊤) (coordinates M i) ⟶ space M hM :=
  colimit.ι (gluingData M hM).functor i

instance (i : Index M) : IsOpenImmersion (chartMap M hM i) := by
  dsimp only [chartMap]
  infer_instance

/-- The glued projection recovers the projection of every actual projective chart. -/
@[reassoc (attr := simp)]
lemma chart_projection (i : Index M) :
    chartMap M hM i ≫ projection M hM =
      ProjectiveSpace.affineProjection i.val.toScheme (coordinates M i) ≫ i.val.ι :=
  (gluingData M hM).ι_toBase i

/-- The actual base change of the glued scheme to a chart is its projective space. -/
lemma chart_isPullback (i : Index M) :
    IsPullback (ProjectiveSpace.affineProjection i.val.toScheme (coordinates M i))
      (chartMap M hM i) i.val.ι (projection M hM) :=
  (gluingData M hM).isPullback_natTrans_ι_toBase i

/-- The actual affine projective charts cover the glued scheme. -/
def cover : (space M hM).OpenCover := (gluingData M hM).cover

/-- The inverse image of each affine free open is exactly its projective chart. -/
lemma projection_preimage (i : Index M) :
    projection M hM ⁻¹ᵁ i.val = (chartMap M hM i).opensRange := by
  simpa only [space, projection, chartMap, AffineFiniteFreeAtlas.cover,
    Scheme.Opens.opensRange_ι] using
    (gluingData M hM).toBase_preimage_eq_opensRange_ι i

end FLT.Mazur.LocallyFreeDualProjectiveAtlas
