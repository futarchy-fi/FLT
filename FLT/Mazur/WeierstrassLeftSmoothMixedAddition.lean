/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTransportedComparison
public import FLT.Mazur.WeierstrassMixedProductCover

/-!
# Integral translation on mixed projective input charts

The full Y/Z, Z/Y and Z/Z input opens with smooth first factor carry addition
into the original cubic. Their polynomial and affine formulas descend on
actual scheme overlaps, allowing singular second inputs and arbitrary coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (b c : Bool) (ha : b = false ∨ c = false)
local notation "j" => productChartCoordinate b
local notation "k" => productChartCoordinate c

/-- The original two-domain cover pulled back to the full left smooth input open. -/
def leftSmoothMixedCover : (leftSmoothProductChartOpen W b c).toScheme.OpenCover :=
  (mixedProductOpenCover W j k (by cases b <;> simp [productChartCoordinate])
    (by cases c <;> simp [productChartCoordinate])
    (by
      rcases ha with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)).pullback₁
      (leftSmoothProductChartOpen W b c).ι

/-- The pulled-back cover retains the original affine or polynomial chart. -/
def leftSmoothMixedProjection (d : Bool) :
    (leftSmoothMixedCover W b c ha).X d ⟶ Spec (mixedProductCoverRing W j k d) :=
  pullback.snd _ _

/-- Both projections retain the original input pair. -/
@[reassoc] theorem leftSmoothMixedProjection_inputs (d : Bool) :
    leftSmoothMixedProjection W b c ha d ≫ mixedProductCoverInclusion W j k d =
      (leftSmoothMixedCover W b c ha).f d ≫ (leftSmoothProductChartOpen W b c).ι :=
  pullback.condition.symm

/-- The affine member normalizes into the enlarged left smooth affine overlap. -/
def leftSmoothMixedAffineLift :
    (leftSmoothMixedCover W b c ha).X true ⟶ (leftSmoothAffineOverlapOpen W b c).toScheme :=
  IsOpenImmersion.lift (leftSmoothAffineOverlapOpen W b c).ι
    (leftSmoothMixedProjection W b c ha true) (by
      rw [Scheme.Opens.range_ι, leftSmoothAffineOverlapOpen_eq]
      rintro _ ⟨p, rfl⟩
      change (leftSmoothMixedProjection W b c ha true ≫
        mixedProductCoverInclusion W j k true) p ∈ leftSmoothProductChartOpen W b c
      rw [leftSmoothMixedProjection_inputs]
      exact ((leftSmoothMixedCover W b c ha).f true p).property)

/-- The normalization lift preserves the actual overlap projection. -/
@[reassoc] theorem leftSmoothMixedAffineLift_inclusion :
    leftSmoothMixedAffineLift W b c ha ≫ (leftSmoothAffineOverlapOpen W b c).ι =
      leftSmoothMixedProjection W b c ha true := IsOpenImmersion.lift_fac _ _ _

/-- The normalized affine member has exactly the original projective inputs. -/
@[reassoc] theorem leftSmoothMixedAffineLift_inputs :
    leftSmoothMixedAffineLift W b c ha ≫ leftSmoothAffineOverlapInput W b c =
      (leftSmoothMixedCover W b c ha).f true ≫ (leftSmoothProductChartOpen W b c).ι := by
  rw [leftSmoothAffineOverlapInput, leftSmoothMixedAffineLift_inclusion_assoc]
  exact leftSmoothMixedProjection_inputs W b c ha true

/-- Actual affine and polynomial laws on the complete two-member input cover. -/
def leftSmoothMixedLocal (d : Bool) :
    (leftSmoothMixedCover W b c ha).X d ⟶ integralCurve W :=
  match d with
  | true => leftSmoothMixedAffineLift W b c ha ≫ leftSmoothAffineOverlapAddition W b c
  | false => leftSmoothMixedProjection W b c ha false ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom) ≫
        integralCurveChart W 2

/-- The affine and polynomial formulas agree on every actual common input scheme. -/
theorem leftSmoothMixedLocal_commonScheme (d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothMixedCover W b c ha).X d)
    (g : X ⟶ (leftSmoothMixedCover W b c ha).X e)
    (h : f ≫ (leftSmoothMixedCover W b c ha).f d =
      g ≫ (leftSmoothMixedCover W b c ha).f e) :
    f ≫ leftSmoothMixedLocal W b c ha d = g ≫ leftSmoothMixedLocal W b c ha e := by
  have mixed {Y : Scheme.{u}} (u : Y ⟶ (leftSmoothMixedCover W b c ha).X true)
      (v : Y ⟶ (leftSmoothMixedCover W b c ha).X false)
      (huv : u ≫ (leftSmoothMixedCover W b c ha).f true =
        v ≫ (leftSmoothMixedCover W b c ha).f false) :
      u ≫ leftSmoothMixedLocal W b c ha true =
        v ≫ leftSmoothMixedLocal W b c ha false := by
    have hi : (u ≫ leftSmoothMixedAffineLift W b c ha) ≫
        leftSmoothAffineOverlapInput W b c =
      (v ≫ leftSmoothMixedProjection W b c ha false) ≫
        projectiveAdditionInclusion W j k 2 := by
      rw [Category.assoc, leftSmoothMixedAffineLift_inputs]
      change _ = (v ≫ leftSmoothMixedProjection W b c ha false) ≫
        mixedProductCoverInclusion W j k false
      rw [Category.assoc, leftSmoothMixedProjection_inputs,
        ← Category.assoc, ← Category.assoc, huv]
    simpa only [leftSmoothMixedLocal, Category.assoc] using
      leftSmoothAffineOverlap_polynomial W b c 2
        (u ≫ leftSmoothMixedAffineLift W b c ha)
        (v ≫ leftSmoothMixedProjection W b c ha false) hi
  cases d <;> cases e
  · exact congrArg (fun a => a ≫ leftSmoothMixedLocal W b c ha false)
      ((cancel_mono ((leftSmoothMixedCover W b c ha).f false)).mp h)
  · exact (mixed g f h.symm).symm
  · exact mixed f g h
  · exact congrArg (fun a => a ≫ leftSmoothMixedLocal W b c ha true)
      ((cancel_mono ((leftSmoothMixedCover W b c ha).f true)).mp h)

/-- The enlarged regular addition on every mixed projective input chart. -/
def leftSmoothMixedAddition :
    (leftSmoothProductChartOpen W b c).toScheme ⟶ integralCurve W :=
  (leftSmoothMixedCover W b c ha).glueMorphisms (leftSmoothMixedLocal W b c ha)
    (fun d e => leftSmoothMixedLocal_commonScheme W b c ha d e _ _ pullback.condition)

/-- The glued law retains its actual affine and polynomial formulas. -/
@[reassoc] theorem leftSmoothMixedLocal_glued (d : Bool) :
    (leftSmoothMixedCover W b c ha).f d ≫ leftSmoothMixedAddition W b c ha =
      leftSmoothMixedLocal W b c ha d :=
  (leftSmoothMixedCover W b c ha).ι_glueMorphisms _ _ d

end FLT.Mazur.WeierstrassIntegralChart
