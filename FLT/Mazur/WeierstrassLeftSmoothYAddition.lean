/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTransportedComparison
public import FLT.Mazur.WeierstrassYProductCover

/-!
# Integral translation on the complete Y/Y input open

The three original Y/Y domains cover all inputs with smooth first factor.
Their actual affine, polynomial and infinity laws glue, including on nonreduced
common schemes and with singular second inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Pull the complete original Y/Y cover back to the left smooth input open. -/
def leftSmoothYCover : (leftSmoothProductChartOpen W true true).toScheme.OpenCover :=
  (yProductOpenCover W).pullback₁ (leftSmoothProductChartOpen W true true).ι

/-- Each pulled-back domain retains its original formula ring. -/
def leftSmoothYProjection (i : YProductCoverIndex) :
    (leftSmoothYCover W).X i ⟶ Spec (yProductCoverRing W i) := pullback.snd _ _

/-- Both projections describe the same original input pair. -/
@[reassoc] theorem leftSmoothYProjection_inputs (i : YProductCoverIndex) :
    leftSmoothYProjection W i ≫ yProductCoverInclusion W i =
      (leftSmoothYCover W).f i ≫ (leftSmoothProductChartOpen W true true).ι :=
  pullback.condition.symm

/-- The affine member lifts into the enlarged affine overlap. -/
def leftSmoothYAffineLift :
    (leftSmoothYCover W).X .affine ⟶ (leftSmoothAffineOverlapOpen W true true).toScheme :=
  IsOpenImmersion.lift (leftSmoothAffineOverlapOpen W true true).ι
    (leftSmoothYProjection W .affine) (by
      rw [Scheme.Opens.range_ι, leftSmoothAffineOverlapOpen_eq]
      rintro _ ⟨p, rfl⟩
      change (leftSmoothYProjection W .affine ≫ yProductCoverInclusion W .affine) p ∈
        leftSmoothProductChartOpen W true true
      rw [leftSmoothYProjection_inputs]
      exact ((leftSmoothYCover W).f .affine p).property)

/-- The lift preserves the overlap projection. -/
@[reassoc] theorem leftSmoothYAffineLift_inclusion :
    leftSmoothYAffineLift W ≫ (leftSmoothAffineOverlapOpen W true true).ι =
      leftSmoothYProjection W .affine := IsOpenImmersion.lift_fac _ _ _

/-- The lift preserves the actual projective input pair. -/
@[reassoc] theorem leftSmoothYAffineLift_inputs :
    leftSmoothYAffineLift W ≫ leftSmoothAffineOverlapInput W true true =
      (leftSmoothYCover W).f .affine ≫ (leftSmoothProductChartOpen W true true).ι := by
  rw [leftSmoothAffineOverlapInput, leftSmoothYAffineLift_inclusion_assoc]
  exact leftSmoothYProjection_inputs W .affine

/-- Actual curve-valued formulas on the three pulled-back input domains. -/
def leftSmoothYLocal (i : YProductCoverIndex) :
    (leftSmoothYCover W).X i ⟶ integralCurve W :=
  match i with
  | .affine => leftSmoothYAffineLift W ≫ leftSmoothAffineOverlapAddition W true true
  | .polynomial => leftSmoothYProjection W .polynomial ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 2).toRingHom) ≫
        integralCurveChart W 2
  | .infinity => leftSmoothYProjection W .infinity ≫
      infinityAdditionSpec W ≫ integralCurveChart W 1

/-- Affine and polynomial laws agree on the actual pulled-back domains. -/
theorem leftSmoothYLocal_affine_polynomial {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothYCover W).X .affine)
    (g : X ⟶ (leftSmoothYCover W).X .polynomial)
    (h : f ≫ (leftSmoothYCover W).f .affine = g ≫ (leftSmoothYCover W).f .polynomial) :
    f ≫ leftSmoothYLocal W .affine = g ≫ leftSmoothYLocal W .polynomial := by
  apply leftSmoothAffineOverlap_polynomial W true true 2
    (f ≫ leftSmoothYAffineLift W) (g ≫ leftSmoothYProjection W .polynomial)
  change _ = (g ≫ leftSmoothYProjection W .polynomial) ≫
    yProductCoverInclusion W .polynomial
  rw [Category.assoc, leftSmoothYAffineLift_inputs, Category.assoc,
    leftSmoothYProjection_inputs, ← Category.assoc, ← Category.assoc, h]

/-- Affine and infinity laws agree on the actual pulled-back domains. -/
theorem leftSmoothYLocal_affine_infinity {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothYCover W).X .affine)
    (g : X ⟶ (leftSmoothYCover W).X .infinity)
    (h : f ≫ (leftSmoothYCover W).f .affine = g ≫ (leftSmoothYCover W).f .infinity) :
    f ≫ leftSmoothYLocal W .affine = g ≫ leftSmoothYLocal W .infinity := by
  apply leftSmoothAffineOverlap_infinity W
    (f ≫ leftSmoothYAffineLift W) (g ≫ leftSmoothYProjection W .infinity)
  change _ = (g ≫ leftSmoothYProjection W .infinity) ≫
    yProductCoverInclusion W .infinity
  rw [Category.assoc, leftSmoothYAffineLift_inputs, Category.assoc,
    leftSmoothYProjection_inputs, ← Category.assoc, ← Category.assoc, h]

/-- Infinity and polynomial laws retain their original boundary comparison. -/
theorem leftSmoothYLocal_infinity_polynomial {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothYCover W).X .infinity)
    (g : X ⟶ (leftSmoothYCover W).X .polynomial)
    (h : f ≫ (leftSmoothYCover W).f .infinity = g ≫ (leftSmoothYCover W).f .polynomial) :
    f ≫ leftSmoothYLocal W .infinity = g ≫ leftSmoothYLocal W .polynomial := by
  apply infinityPolynomial_curve_eq W 2
    (f ≫ leftSmoothYProjection W .infinity) (g ≫ leftSmoothYProjection W .polynomial)
  change (f ≫ leftSmoothYProjection W .infinity) ≫ yProductCoverInclusion W .infinity =
    (g ≫ leftSmoothYProjection W .polynomial) ≫ yProductCoverInclusion W .polynomial
  rw [Category.assoc, leftSmoothYProjection_inputs, Category.assoc,
    leftSmoothYProjection_inputs, ← Category.assoc, ← Category.assoc, h]

/-- All three formulas agree on every common input scheme, including nilpotents. -/
theorem leftSmoothYLocal_commonScheme (i j : YProductCoverIndex) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothYCover W).X i) (g : X ⟶ (leftSmoothYCover W).X j)
    (h : f ≫ (leftSmoothYCover W).f i = g ≫ (leftSmoothYCover W).f j) :
    f ≫ leftSmoothYLocal W i = g ≫ leftSmoothYLocal W j := by
  have same (k : YProductCoverIndex) (a b : X ⟶ (leftSmoothYCover W).X k)
      (hab : a ≫ (leftSmoothYCover W).f k = b ≫ (leftSmoothYCover W).f k) :
      a ≫ leftSmoothYLocal W k = b ≫ leftSmoothYLocal W k :=
    congrArg (fun t => t ≫ leftSmoothYLocal W k)
      ((cancel_mono ((leftSmoothYCover W).f k)).mp hab)
  cases i <;> cases j
  · exact same _ f g h
  · exact leftSmoothYLocal_affine_polynomial W f g h
  · exact leftSmoothYLocal_affine_infinity W f g h
  · exact (leftSmoothYLocal_affine_polynomial W g f h.symm).symm
  · exact same _ f g h
  · exact (leftSmoothYLocal_infinity_polynomial W g f h.symm).symm
  · exact (leftSmoothYLocal_affine_infinity W g f h.symm).symm
  · exact leftSmoothYLocal_infinity_polynomial W f g h
  · exact same _ f g h

/-- Integral addition on the complete left smooth Y/Y input open. -/
def leftSmoothYAddition :
    (leftSmoothProductChartOpen W true true).toScheme ⟶ integralCurve W :=
  (leftSmoothYCover W).glueMorphisms (leftSmoothYLocal W)
    (fun i j => leftSmoothYLocal_commonScheme W i j _ _ pullback.condition)

/-- The glued law retains each original formula on its actual domain. -/
@[reassoc] theorem leftSmoothYLocal_glued (i : YProductCoverIndex) :
    (leftSmoothYCover W).f i ≫ leftSmoothYAddition W = leftSmoothYLocal W i :=
  (leftSmoothYCover W).ι_glueMorphisms _ _ i

end FLT.Mazur.WeierstrassIntegralChart
