/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothProductOpen

/-!
# The smooth product open is the categorical product of smooth factors

The open in the original projective product represents pairs of smooth points
over the coefficient base. Explicit inverse morphisms identify it with the
fiber product of the two actual smooth curves.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The categorical product of the two relative smooth curves over their coefficient base. -/
abbrev smoothFactorProduct := pullback (integralSmoothStructure W) (integralSmoothStructure W)

/-- The first projection of the smooth product open, landing in the smooth curve. -/
def smoothProductFst :
    (smoothCurveProductOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((smoothCurveProductOpen W).ι ≫ pullback.fst _ _) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.property.1)

/-- The second projection of the smooth product open, landing in the smooth curve. -/
def smoothProductSnd :
    (smoothCurveProductOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((smoothCurveProductOpen W).ι ≫ pullback.snd _ _) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.property.2)

/-- The first smooth projection retains the original first factor. -/
@[reassoc] theorem smoothProductFst_inclusion :
    smoothProductFst W ≫ (integralSmoothOpen W).ι =
      (smoothCurveProductOpen W).ι ≫ pullback.fst _ _ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The second smooth projection retains the original second factor. -/
@[reassoc] theorem smoothProductSnd_inclusion :
    smoothProductSnd W ≫ (integralSmoothOpen W).ι =
      (smoothCurveProductOpen W).ι ≫ pullback.snd _ _ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The two smooth projections agree over the base. -/
theorem smoothProduct_condition :
    smoothProductFst W ≫ integralSmoothStructure W =
      smoothProductSnd W ≫ integralSmoothStructure W := by
  rw [integralSmoothStructure, smoothProductFst_inclusion_assoc,
    smoothProductSnd_inclusion_assoc, pullback.condition]

/-- The map from the smooth product open to the categorical smooth-factor product. -/
def smoothProductToFactors : (smoothCurveProductOpen W).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (smoothProductFst W) (smoothProductSnd W) (smoothProduct_condition W)

/-- The categorical smooth-factor product maps into the original projective product. -/
def smoothFactorsInclusion : smoothFactorProduct W ⟶ integralCurveProduct W :=
  pullback.lift (pullback.fst _ _ ≫ (integralSmoothOpen W).ι)
    (pullback.snd _ _ ≫ (integralSmoothOpen W).ι) (by
      simpa only [Category.assoc, integralSmoothStructure] using
        (pullback.condition (f := integralSmoothStructure W) (g := integralSmoothStructure W)))

/-- The categorical smooth-factor product lies in the actual smooth product open. -/
def smoothFactorsToProduct : smoothFactorProduct W ⟶ (smoothCurveProductOpen W).toScheme :=
  IsOpenImmersion.lift (smoothCurveProductOpen W).ι (smoothFactorsInclusion W) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    constructor
    · change (smoothFactorsInclusion W ≫ pullback.fst _ _) p ∈ integralSmoothOpen W
      rw [smoothFactorsInclusion, pullback.lift_fst]
      exact (pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) p).property
    · change (smoothFactorsInclusion W ≫ pullback.snd _ _) p ∈ integralSmoothOpen W
      rw [smoothFactorsInclusion, pullback.lift_snd]
      exact (pullback.snd (integralSmoothStructure W) (integralSmoothStructure W) p).property)

/-- The restricted inclusion retains the original pair of smooth factors. -/
@[reassoc] theorem smoothFactorsToProduct_inclusion :
    smoothFactorsToProduct W ≫ (smoothCurveProductOpen W).ι = smoothFactorsInclusion W :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map to categorical factors retains the original global product inclusion. -/
@[reassoc] theorem smoothProductToFactors_inclusion :
    smoothProductToFactors W ≫ smoothFactorsInclusion W = (smoothCurveProductOpen W).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_fst,
      ← Category.assoc, smoothProductToFactors, pullback.lift_fst, smoothProductFst_inclusion]
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_snd,
      ← Category.assoc, smoothProductToFactors, pullback.lift_snd, smoothProductSnd_inclusion]

/-- The open restriction is exactly the categorical product of the two smooth curves. -/
def smoothProductFactorsIso : (smoothCurveProductOpen W).toScheme ≅ smoothFactorProduct W where
  hom := smoothProductToFactors W
  inv := smoothFactorsToProduct W
  hom_inv_id := by
    apply (cancel_mono (smoothCurveProductOpen W).ι).mp
    rw [Category.assoc, smoothFactorsToProduct_inclusion,
      smoothProductToFactors_inclusion, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (integralSmoothOpen W).ι).mp
      simp only [Category.assoc, smoothProductToFactors, pullback.lift_fst_assoc,
        smoothProductFst_inclusion, Category.id_comp]
      rw [← Category.assoc, smoothFactorsToProduct_inclusion,
        smoothFactorsInclusion, pullback.lift_fst]
    · apply (cancel_mono (integralSmoothOpen W).ι).mp
      simp only [Category.assoc, smoothProductToFactors, pullback.lift_snd_assoc,
        smoothProductSnd_inclusion, Category.id_comp]
      rw [← Category.assoc, smoothFactorsToProduct_inclusion,
        smoothFactorsInclusion, pullback.lift_snd]

end FLT.Mazur.WeierstrassIntegralChart
