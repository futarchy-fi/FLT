/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFactorAddition
public import FLT.Mazur.WeierstrassSmoothNegation
public import FLT.Mazur.WeierstrassNegationPairSections

/-!
# Smooth graphs of a point and its negation

The involution on the smooth curve determines both inverse graphs in its
categorical product. Their inclusions recover the original projective graphs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Pair a smooth point with its smooth negation. -/
def smoothFactorRightNegation : (integralSmoothOpen W).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (𝟙 _) (integralSmoothNegation W)
    (by rw [Category.id_comp, integralSmoothNegation_structure])

/-- Pair the smooth negation with the original point. -/
def smoothFactorLeftNegation : (integralSmoothOpen W).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (integralSmoothNegation W) (𝟙 _)
    (by rw [Category.id_comp, integralSmoothNegation_structure])

/-- The right smooth graph retains the actual original negation pair. -/
@[reassoc] theorem smoothFactorRightNegation_inclusion :
    smoothFactorRightNegation W ≫ smoothFactorsInclusion W =
      (integralSmoothOpen W).ι ≫ integralCurveRightNegation W := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_fst, ← Category.assoc,
      smoothFactorRightNegation, pullback.lift_fst, Category.id_comp,
      Category.assoc, integralCurveRightNegation_fst, Category.comp_id]
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_snd, ← Category.assoc,
      smoothFactorRightNegation, pullback.lift_snd, integralSmoothNegation_inclusion,
      Category.assoc, integralCurveRightNegation_snd]

/-- The left smooth graph retains the actual original negation pair. -/
@[reassoc] theorem smoothFactorLeftNegation_inclusion :
    smoothFactorLeftNegation W ≫ smoothFactorsInclusion W =
      (integralSmoothOpen W).ι ≫ integralCurveLeftNegation W := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_fst, ← Category.assoc,
      smoothFactorLeftNegation, pullback.lift_fst, integralSmoothNegation_inclusion,
      Category.assoc, integralCurveLeftNegation_fst]
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_snd, ← Category.assoc,
      smoothFactorLeftNegation, pullback.lift_snd, Category.id_comp,
      Category.assoc, integralCurveLeftNegation_snd, Category.comp_id]

/-- The right inverse graph in the full smooth product open. -/
def smoothProductRightNegation :
    (integralSmoothOpen W).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  smoothFactorRightNegation W ≫ smoothFactorsToProduct W

/-- The left inverse graph in the full smooth product open. -/
def smoothProductLeftNegation :
    (integralSmoothOpen W).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  smoothFactorLeftNegation W ≫ smoothFactorsToProduct W

/-- The right inverse graph preserves the original projective inputs. -/
@[reassoc] theorem smoothProductRightNegation_inclusion :
    smoothProductRightNegation W ≫ (smoothCurveProductOpen W).ι =
      (integralSmoothOpen W).ι ≫ integralCurveRightNegation W := by
  rw [smoothProductRightNegation, Category.assoc, smoothFactorsToProduct_inclusion,
    smoothFactorRightNegation_inclusion]

/-- The left inverse graph preserves the original projective inputs. -/
@[reassoc] theorem smoothProductLeftNegation_inclusion :
    smoothProductLeftNegation W ≫ (smoothCurveProductOpen W).ι =
      (integralSmoothOpen W).ι ≫ integralCurveLeftNegation W := by
  rw [smoothProductLeftNegation, Category.assoc, smoothFactorsToProduct_inclusion,
    smoothFactorLeftNegation_inclusion]

/-- Precomposing the right graph with negation gives the left graph. -/
@[reassoc] theorem smoothNegation_rightGraph :
    integralSmoothNegation W ≫ smoothProductRightNegation W =
      smoothProductLeftNegation W := by
  apply (cancel_mono (smoothCurveProductOpen W).ι).mp
  rw [Category.assoc, smoothProductRightNegation_inclusion,
    integralSmoothNegation_inclusion_assoc, integralCurveNegation_rightNegation,
    smoothProductLeftNegation_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
