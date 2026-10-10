/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteFreeDirectedCover
public import FLT.Mazur.FiniteFreeProjectiveAtlasDiagram

/-!
# Gluing the projective quotient charts over the actual base

A locally finite free sheaf supplies its own affine free atlas. Relative gluing
constructs a scheme over the original base with cartesian projective chart
squares. These are quotients of the homogeneous-generator module; constructing
the intended section-line bundle requires the dual convention.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFreeProjectiveQuotient
open FCurve AffineFiniteFreeAtlas
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)

instance (i : Index M) : IsAffine ((opens M).obj i).toScheme := i.property.1

/-- The actual quotient-chart gluing datum supplied by local finite freeness. -/
def gluingData : (AffineFiniteFreeAtlas.cover M hM).RelativeGluingData where
  functor := FiniteFreeProjectiveAtlas.diagram M (opens M) (coordinates M) (chart M)
  natTrans :=
    { app i := ProjectiveSpace.affineProjection i.val.toScheme (coordinates M i)
      naturality := by
        intro i j f
        exact FiniteFreeChartTransitions.chartInclusion_projection M f.le (chart M i) (chart M j) }
  equifibered := by
    intro i j f
    exact FiniteFreeChartTransitions.chartInclusion_isPullback M f.le (chart M i) (chart M j)

/-- The glued projective quotient scheme of the locally finite free sheaf. -/
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

end FLT.Mazur.LocallyFreeProjectiveQuotient
