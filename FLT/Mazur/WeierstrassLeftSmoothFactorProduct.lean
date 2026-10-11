/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothProductOpen

/-!
# The left smooth product open represents smooth by unrestricted pairs

Explicit inverse morphisms identify the open input domain with the categorical
product of the original smooth curve and the whole original cubic over the base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The product of the original smooth curve and the whole original cubic. -/
abbrev leftSmoothFactorProduct := pullback (integralSmoothStructure W) (integralCurveStructure W)

/-- The first projection lands in the original relative smooth locus. -/
def leftSmoothProductFst :
    (leftSmoothCurveProductOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((leftSmoothCurveProductOpen W).ι ≫ pullback.fst _ _) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.property)

/-- The second projection retains every point of the original cubic. -/
def leftSmoothProductSnd : (leftSmoothCurveProductOpen W).toScheme ⟶ integralCurve W :=
  (leftSmoothCurveProductOpen W).ι ≫ pullback.snd _ _

/-- The smooth first projection retains the actual original point. -/
@[reassoc] theorem leftSmoothProductFst_inclusion :
    leftSmoothProductFst W ≫ (integralSmoothOpen W).ι =
      (leftSmoothCurveProductOpen W).ι ≫ pullback.fst _ _ :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both factors agree over the original coefficient scheme. -/
theorem leftSmoothProduct_condition :
    leftSmoothProductFst W ≫ integralSmoothStructure W =
      leftSmoothProductSnd W ≫ integralCurveStructure W := by
  rw [integralSmoothStructure, leftSmoothProductFst_inclusion_assoc,
    leftSmoothProductSnd, Category.assoc, pullback.condition]

/-- The left smooth input open maps to the actual categorical factor product. -/
def leftSmoothProductToFactors :
    (leftSmoothCurveProductOpen W).toScheme ⟶ leftSmoothFactorProduct W :=
  pullback.lift (leftSmoothProductFst W) (leftSmoothProductSnd W)
    (leftSmoothProduct_condition W)

/-- The categorical factors retain their two original curve inputs. -/
def leftSmoothFactorsInclusion : leftSmoothFactorProduct W ⟶ integralCurveProduct W :=
  pullback.lift (pullback.fst _ _ ≫ (integralSmoothOpen W).ι) (pullback.snd _ _) (by
    simpa only [Category.assoc, integralSmoothStructure] using
      (pullback.condition (f := integralSmoothStructure W) (g := integralCurveStructure W)))

/-- The categorical factor product lies in the complete left smooth input open. -/
def leftSmoothFactorsToProduct :
    leftSmoothFactorProduct W ⟶ (leftSmoothCurveProductOpen W).toScheme :=
  IsOpenImmersion.lift (leftSmoothCurveProductOpen W).ι (leftSmoothFactorsInclusion W) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    change (leftSmoothFactorsInclusion W ≫ pullback.fst _ _) p ∈ integralSmoothOpen W
    rw [leftSmoothFactorsInclusion, pullback.lift_fst]
    exact (pullback.fst (integralSmoothStructure W) (integralCurveStructure W) p).property)

/-- Passing to the input open preserves the original pair. -/
@[reassoc] theorem leftSmoothFactorsToProduct_inclusion :
    leftSmoothFactorsToProduct W ≫ (leftSmoothCurveProductOpen W).ι =
      leftSmoothFactorsInclusion W := IsOpenImmersion.lift_fac _ _ _

/-- Passing to categorical factors preserves the original input inclusion. -/
@[reassoc] theorem leftSmoothProductToFactors_inclusion :
    leftSmoothProductToFactors W ≫ leftSmoothFactorsInclusion W =
      (leftSmoothCurveProductOpen W).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_fst,
      ← Category.assoc, leftSmoothProductToFactors, pullback.lift_fst,
      leftSmoothProductFst_inclusion]
  · rw [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_snd,
      leftSmoothProductToFactors, pullback.lift_snd]
    rfl

/-- The original left smooth open is exactly the smooth by unrestricted factor product. -/
def leftSmoothProductFactorsIso :
    (leftSmoothCurveProductOpen W).toScheme ≅ leftSmoothFactorProduct W where
  hom := leftSmoothProductToFactors W
  inv := leftSmoothFactorsToProduct W
  hom_inv_id := by
    apply (cancel_mono (leftSmoothCurveProductOpen W).ι).mp
    rw [Category.assoc, leftSmoothFactorsToProduct_inclusion,
      leftSmoothProductToFactors_inclusion, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (integralSmoothOpen W).ι).mp
      simp only [Category.assoc, leftSmoothProductToFactors, pullback.lift_fst_assoc,
        leftSmoothProductFst_inclusion, Category.id_comp]
      rw [← Category.assoc, leftSmoothFactorsToProduct_inclusion,
        leftSmoothFactorsInclusion, pullback.lift_fst]
    · simp only [Category.assoc, leftSmoothProductToFactors, pullback.lift_snd,
        Category.id_comp, leftSmoothProductSnd]
      rw [← Category.assoc, leftSmoothFactorsToProduct_inclusion,
        leftSmoothFactorsInclusion, pullback.lift_snd]

end FLT.Mazur.WeierstrassIntegralChart
