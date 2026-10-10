/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFactorAddition
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# The two smooth zero graphs

Pairing a smooth point with the zero section stays in the actual smooth-factor
product. These graphs agree with the original projective zero graphs, so the
original local identity calculations apply to the new smooth addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The left-zero graph in the categorical product of the smooth curves. -/
def smoothFactorLeftZero : (integralSmoothOpen W).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (integralSmoothStructure W ≫ integralSmoothZero W) (𝟙 _)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id, Category.id_comp])

/-- The right-zero graph in the categorical product of the smooth curves. -/
def smoothFactorRightZero : (integralSmoothOpen W).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (𝟙 _) (integralSmoothStructure W ≫ integralSmoothZero W)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id, Category.id_comp])

/-- The left smooth zero graph preserves the original projective input pair. -/
@[reassoc] theorem smoothFactorLeftZero_inclusion :
    smoothFactorLeftZero W ≫ smoothFactorsInclusion W =
      (integralSmoothOpen W).ι ≫ integralCurveLeftZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_fst, ← Category.assoc,
      smoothFactorLeftZero, pullback.lift_fst, Category.assoc, integralSmoothZero_inclusion,
      Category.assoc (integralSmoothOpen W).ι (integralCurveLeftZero W),
      integralCurveLeftZero_fst]
    rfl
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_snd, ← Category.assoc,
      smoothFactorLeftZero, pullback.lift_snd, Category.id_comp,
      Category.assoc, integralCurveLeftZero_snd, Category.comp_id]

/-- The right smooth zero graph preserves the original projective input pair. -/
@[reassoc] theorem smoothFactorRightZero_inclusion :
    smoothFactorRightZero W ≫ smoothFactorsInclusion W =
      (integralSmoothOpen W).ι ≫ integralCurveRightZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_fst, ← Category.assoc,
      smoothFactorRightZero, pullback.lift_fst, Category.id_comp,
      Category.assoc, integralCurveRightZero_fst, Category.comp_id]
  · rw [Category.assoc, smoothFactorsInclusion, pullback.lift_snd, ← Category.assoc,
      smoothFactorRightZero, pullback.lift_snd, Category.assoc, integralSmoothZero_inclusion,
      Category.assoc (integralSmoothOpen W).ι (integralCurveRightZero W),
      integralCurveRightZero_snd]
    rfl

/-- The left-zero graph as a morphism into the full smooth product open. -/
def smoothProductLeftZero :
    (integralSmoothOpen W).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  smoothFactorLeftZero W ≫ smoothFactorsToProduct W

/-- The right-zero graph as a morphism into the full smooth product open. -/
def smoothProductRightZero :
    (integralSmoothOpen W).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  smoothFactorRightZero W ≫ smoothFactorsToProduct W

/-- The left graph retains the original zero pairing after inclusion into the product. -/
@[reassoc] theorem smoothProductLeftZero_inclusion :
    smoothProductLeftZero W ≫ (smoothCurveProductOpen W).ι =
      (integralSmoothOpen W).ι ≫ integralCurveLeftZero W := by
  rw [smoothProductLeftZero, Category.assoc, smoothFactorsToProduct_inclusion,
    smoothFactorLeftZero_inclusion]

/-- The right graph retains the original zero pairing after inclusion into the product. -/
@[reassoc] theorem smoothProductRightZero_inclusion :
    smoothProductRightZero W ≫ (smoothCurveProductOpen W).ι =
      (integralSmoothOpen W).ι ≫ integralCurveRightZero W := by
  rw [smoothProductRightZero, Category.assoc, smoothFactorsToProduct_inclusion,
    smoothFactorRightZero_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
