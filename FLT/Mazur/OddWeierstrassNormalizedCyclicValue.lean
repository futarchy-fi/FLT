/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedCyclicParameter

/-!
# Exact cyclic values of normalized odd parameters

The coefficient projection and inverse normalization retain every original
cyclic section, without distinctness of cyclic labels.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))} {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (T ⟶ (auxiliaryPullbackGroup g).X))

/-- Each normalized cyclic value is its actual normalized-group coefficient projection. -/
theorem auxiliaryNormalizedCyclicHomPoint_value (i : Multiplicative (ZMod n)) :
    (auxiliaryNormalizedCyclicHomPoint g φ ≫ value universalGroup _ i).left =
      (auxiliaryNormalizedCyclicMarking g φ i).left ≫
        (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) := by
  rw [auxiliaryNormalizedCyclicHomPoint_def]
  exact (cartesianHomParameter_value (auxiliaryNormalizedCoefficientBase g)
    (integralCurveGroup oddChartEquation oddChart_discriminant) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizedCoefficientGroupIso g) _
    (liftMarking _ _ (auxiliaryNormalizedCyclicMarking g φ)) i).trans (by
      rw [liftMarking_value]
      rfl)

variable (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelThree)

/-- The paired parameter retains the exact coordinate projection for every cyclic label. -/
theorem auxiliaryNormalizedCyclicParameter_value (i : Multiplicative (ZMod n)) :
    (auxiliaryNormalizedCyclicParameter g p φ).left ≫
        (cyclicHomParameter n ≫ value universalGroup _ i).left =
      (auxiliaryNormalizedCyclicMarking g φ i).left ≫
        (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) := by
  rw [← Over.comp_left, auxiliaryNormalizedCyclicParameter_cyclic_assoc]
  exact auxiliaryNormalizedCyclicHomPoint_value g φ i

end FLT.Mazur.OddWeierstrassParameter
