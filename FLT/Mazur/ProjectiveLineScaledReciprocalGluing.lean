/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonScaledReciprocal
public import FLT.Mazur.ProjectiveLineScaling

/-!
# Gluing full affine charts with the original scaled reciprocal

A reciprocal scale is retained by scaling the complete second affine chart.
This produces the fixed projective line and keeps both original origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The specified scaled reciprocal is the standard inverse-coordinate overlap after scaling. -/
@[reassoc] theorem scaledReciprocal_overlap (a : Kˣ) :
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a).toRingHom) ≫
      overlapLeft K = overlapRight K ≫ chartScaling K a := by
  have H : (PolygonScaledReciprocal.reciprocal a).toRingHom.comp Polynomial.toLaurent =
      LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent.comp (PolygonChartScaling.affine a)) := by
    rw [PolygonChartScaling.toLaurent_affine]
    rfl
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, overlapLeft, overlapRight,
    inversion_hom, chartScaling, Category.assoc] using
      congrArg (fun f => Spec.map (CommRingCat.ofHom f)) H

variable {K} {X : Scheme.{u}} (a : Kˣ) (f g : chart K ⟶ X)
  (h : overlapLeft K ≫ f =
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a).toRingHom) ≫
      overlapLeft K ≫ g)

/-- Glue the two full affine maps using their actual scaled reciprocal transition. -/
def scaledReciprocalDesc : scheme K ⟶ X :=
  pushout.desc f (chartScaling K a ≫ g) (by
    rw [← Category.assoc, scaledReciprocal_overlap, Category.assoc] at h
    exact h)

/-- The first full affine chart retains its original parameter. -/
@[reassoc] theorem scaledReciprocalDesc_left :
    left K ≫ scaledReciprocalDesc a f g h = f := pushout.inl_desc _ _ _

/-- The second full chart retains the exact original scale. -/
@[reassoc] theorem scaledReciprocalDesc_right :
    right K ≫ scaledReciprocalDesc a f g h = chartScaling K a ≫ g :=
  pushout.inr_desc _ _ _

/-- The zero endpoint is the origin of the first original affine chart. -/
@[reassoc] theorem scaledReciprocalDesc_zero :
    zero K ≫ scaledReciprocalDesc a f g h = chartZero K ≫ f := by
  rw [zero, Category.assoc, scaledReciprocalDesc_left]

/-- Scaling the second chart preserves its original origin as the infinity endpoint. -/
@[reassoc] theorem scaledReciprocalDesc_infinity :
    infinity K ≫ scaledReciprocalDesc a f g h = chartZero K ≫ g := by
  rw [infinity, Category.assoc, scaledReciprocalDesc_right,
    ← Category.assoc, chartZero_chartScaling]

end FLT.Mazur.ProjectiveLine
