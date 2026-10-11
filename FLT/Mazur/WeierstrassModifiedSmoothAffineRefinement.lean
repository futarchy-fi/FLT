/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFactorAddition
public import FLT.Mazur.WeierstrassFiveRegularSectionDescent

/-!
# Actual affine output refinements of a modified smooth input

Start with any affine input mapping to the original cubic. The product with
its original smooth locus is covered by inverse images of all three output
charts, then by affine opens. The projection to the affine input is flat
because the original smooth structure is smooth, including in bad reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R A : Type u} [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (c : Spec (.of A) ⟶ integralCurve W)

/-- The entire smooth-input product over an actual affine modified chart. -/
abbrev modifiedSmoothAffineProduct :=
  pullback (integralSmoothStructure W) (c ≫ integralCurveStructure W)

/-- The original addition on the contracted pair. -/
def modifiedSmoothAffineAddition : modifiedSmoothAffineProduct W c ⟶ integralCurve W :=
  leftSmoothPointAddition W (pullback.fst _ _) (pullback.snd _ _ ≫ c)
    (by rw [Category.assoc]; exact pullback.condition)

/-- All three original output domains cover the entire modified input product. -/
def modifiedSmoothOutputCover : (modifiedSmoothAffineProduct W c).OpenCover :=
  (integralCurveOpenCover W).pullback₁ (modifiedSmoothAffineAddition W c)

/-- Actual affine opens of all output domains cover the whole smooth-input product. -/
def modifiedSmoothAffineCover : (modifiedSmoothAffineProduct W c).AffineOpenCover :=
  (modifiedSmoothOutputCover W c).affineRefinement

/-- Each affine member retains the original smooth parameter. -/
def modifiedSmoothAffineParameter (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec ((modifiedSmoothAffineCover W c).X i) ⟶ (integralSmoothOpen W).toScheme :=
  (modifiedSmoothAffineCover W c).f i ≫ pullback.fst _ _

/-- Each affine member retains its map to the actual modified input chart. -/
def modifiedSmoothAffineProjection (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec ((modifiedSmoothAffineCover W c).X i) ⟶ Spec (.of A) :=
  (modifiedSmoothAffineCover W c).f i ≫ pullback.snd _ _

/-- Smooth base change followed by an open immersion proves flatness of each projection. -/
instance modifiedSmoothAffineProjection_flat (i : (modifiedSmoothAffineCover W c).I₀) :
    Flat (modifiedSmoothAffineProjection W c i) := by
  unfold modifiedSmoothAffineProjection
  infer_instance

/-- The ring map to the actual modified input, extracted from its scheme projection. -/
def modifiedSmoothAffineInputHom (i : (modifiedSmoothAffineCover W c).I₀) :
    A →+* (modifiedSmoothAffineCover W c).X i :=
  affineChartRingHom (modifiedSmoothAffineProjection W c i)

/-- Extracting coordinates retains precisely the original projection. -/
@[simp] theorem modifiedSmoothAffineInputHom_spec (i : (modifiedSmoothAffineCover W c).I₀) :
    Spec.map (CommRingCat.ofHom (modifiedSmoothAffineInputHom W c i)) =
      modifiedSmoothAffineProjection W c i := affineChartRingHom_spec _

/-- Flatness is proved on the actual affine cover, rather than required of a test ring. -/
theorem modifiedSmoothAffineInputHom_flat (i : (modifiedSmoothAffineCover W c).I₀) :
    RingHom.Flat (modifiedSmoothAffineInputHom W c i) := by
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (modifiedSmoothAffineInputHom W c i))).mp
  rw [modifiedSmoothAffineInputHom_spec]
  infer_instance

/-- The original pair on every affine member has the same coefficient map. -/
@[reassoc] theorem modifiedSmoothAffineParameter_structure
    (i : (modifiedSmoothAffineCover W c).I₀) :
    modifiedSmoothAffineParameter W c i ≫ integralSmoothStructure W =
      (modifiedSmoothAffineProjection W c i ≫ c) ≫ integralCurveStructure W := by
  simp only [modifiedSmoothAffineParameter, modifiedSmoothAffineProjection, Category.assoc]
  rw [pullback.condition]

/-- Restricting addition to a cover member is addition of its actual original pair. -/
theorem modifiedSmoothAffineCover_addition (i : (modifiedSmoothAffineCover W c).I₀) :
    (modifiedSmoothAffineCover W c).f i ≫ modifiedSmoothAffineAddition W c =
      leftSmoothPointAddition W (modifiedSmoothAffineParameter W c i)
        (modifiedSmoothAffineProjection W c i ≫ c)
        (modifiedSmoothAffineParameter_structure W c i) := by
  unfold modifiedSmoothAffineAddition leftSmoothPointAddition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, modifiedSmoothAffineParameter]
  · simp only [Category.assoc, pullback.lift_snd, modifiedSmoothAffineProjection]

end FLT.Mazur.WeierstrassIntegralChart
