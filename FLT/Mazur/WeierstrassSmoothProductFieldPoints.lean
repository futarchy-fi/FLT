/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTransportedComparison
public import FLT.Mazur.WeierstrassPolynomialFieldSmooth

/-!
# Smooth field points of the projective input charts

Nonsingular coordinates put a field-valued input pair in the actual smooth
product open. On the simultaneous affine overlap the transported addition
therefore has smooth output, for every coefficient equation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (b c : Bool)

/-- Nonsingular input coordinates give a point of the full smooth product open. -/
theorem productFieldPoint_range_smooth
    (f : ChartProduct W (productChartCoordinate b) (productChartCoordinate c) →ₐ[R] K)
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ chartProductLeft W (productChartCoordinate b) (productChartCoordinate c) ∘
        coord W (productChartCoordinate b)))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ chartProductRight W (productChartCoordinate b) (productChartCoordinate c) ∘
        coord W (productChartCoordinate c))) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom)) ⊆ smoothProductChartOpen W b c := by
  have hsl := chartFieldPoint_range_smooth W (productChartCoordinate b)
    (f.comp (chartProductLeft W (productChartCoordinate b) (productChartCoordinate c))) hl
  have hsr := chartFieldPoint_range_smooth W (productChartCoordinate c)
    (f.comp (chartProductRight W (productChartCoordinate b) (productChartCoordinate c))) hr
  rw [smoothProductChartOpen_eq]
  rintro _ ⟨p, rfl⟩
  constructor
  · rw [← integralCurveChart_preimage_smooth]
    have h := hsl ⟨p, rfl⟩
    change (Spec.map (CommRingCat.ofHom (f.toRingHom.comp
      (chartProductLeft W (productChartCoordinate b)
        (productChartCoordinate c)).toRingHom)) ≫ integralCurveChart W
          (productChartCoordinate b)) p ∈ integralSmoothOpen W at h
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at h
    exact h
  · rw [← integralCurveChart_preimage_smooth]
    have h := hsr ⟨p, rfl⟩
    change (Spec.map (CommRingCat.ofHom (f.toRingHom.comp
      (chartProductRight W (productChartCoordinate b)
        (productChartCoordinate c)).toRingHom)) ≫ integralCurveChart W
          (productChartCoordinate c)) p ∈ integralSmoothOpen W at h
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at h
    exact h

/-- Any smooth input map through the affine overlap has the transported smooth lift. -/
def smoothAffineOverlapLift {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ProductOverlap W
      (productChartCoordinate b) (productChartCoordinate c) 2 2)))
    (hs : Set.range (f ≫ integralProductOverlapFst W b c false false) ⊆
      smoothProductChartOpen W b c) : X ⟶ (smoothAffineOverlapOpen W b c).toScheme :=
  IsOpenImmersion.lift (smoothAffineOverlapOpen W b c).ι f (by
    rw [Scheme.Opens.range_ι, smoothAffineOverlapOpen_eq]
    rintro _ ⟨p, rfl⟩
    exact hs ⟨p, rfl⟩)

/-- The smooth overlap lift preserves the original input pair as a scheme morphism. -/
@[reassoc] theorem smoothAffineOverlapLift_input {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ProductOverlap W
      (productChartCoordinate b) (productChartCoordinate c) 2 2)))
    (hs : Set.range (f ≫ integralProductOverlapFst W b c false false) ⊆
      smoothProductChartOpen W b c) :
    smoothAffineOverlapLift W b c f hs ≫ smoothAffineOverlapInput W b c =
      f ≫ integralProductOverlapFst W b c false false := by
  rw [smoothAffineOverlapInput, ← Category.assoc]
  exact congrArg (fun g => g ≫ integralProductOverlapFst W b c false false)
    (IsOpenImmersion.lift_fac _ _ _)

end FLT.Mazur.WeierstrassIntegralChart
