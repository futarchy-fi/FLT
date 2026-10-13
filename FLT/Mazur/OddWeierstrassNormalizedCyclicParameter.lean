/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedMarking
public import FLT.Mazur.OddWeierstrassCyclicHomAuxiliaryScheme
public import FLT.Mazur.CartesianHomMarkingParameter

/-!
# Normalized odd parameters retaining unrestricted cyclic labels

The actual proper normalization carries every cyclic section independently of
the faithful auxiliary labels. Coincident cyclic sections are allowed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))} {n : ℕ}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelThree)
  (φ : Multiplicative (ZMod n) →* (T ⟶ (auxiliaryPullbackGroup g).X))

/-- Transport all original cyclic labels through the actual proper group normalization. -/
def auxiliaryNormalizedCyclicMarking :
    Multiplicative (ZMod n) →* (T ⟶ (auxiliaryNormalizedGroup g).X) :=
  GroupMarkingTransport.transport (auxiliaryPullbackGroup g) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizationGroupIso g).symm φ

/-- Every normalized cyclic section has its exact original inverse-normalization formula. -/
theorem auxiliaryNormalizedCyclicMarking_value (i : Multiplicative (ZMod n)) :
    auxiliaryNormalizedCyclicMarking g φ i =
      φ i ≫ (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom := rfl

variable [NeZero n]

/-- The complete cyclic marking on the actual normalized coefficient base. -/
irreducible_def auxiliaryNormalizedCyclicHomPoint :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶
      homScheme universalGroup (Multiplicative (ZMod n)) :=
  cartesianHomParameter (auxiliaryNormalizedCoefficientBase g)
    (integralCurveGroup oddChartEquation oddChart_discriminant) (auxiliaryNormalizedGroup g)
    (auxiliaryNormalizedCoefficientGroupIso g) _
    (liftMarking _ _ (auxiliaryNormalizedCyclicMarking g φ))

/-- Normalized auxiliary and cyclic labels give an actual odd-chart parameter. -/
def auxiliaryNormalizedCyclicParameter :
    (Over.map (auxiliaryNormalizedCoefficientBase g)).obj T ⟶ cyclicHomAuxiliaryScheme n :=
  cyclicHomLift n (auxiliaryNormalizedLevelPoint g p) (auxiliaryNormalizedCyclicHomPoint g φ)

/-- Pairing retains the complete normalized faithful auxiliary parameter. -/
@[reassoc] theorem auxiliaryNormalizedCyclicParameter_auxiliary :
    auxiliaryNormalizedCyclicParameter g p φ ≫ cyclicHomAuxiliary n =
      auxiliaryNormalizedLevelPoint g p := cyclicHomLift_auxiliary n _ _

/-- Pairing retains every normalized cyclic label, without a faithfulness requirement. -/
@[reassoc] theorem auxiliaryNormalizedCyclicParameter_cyclic :
    auxiliaryNormalizedCyclicParameter g p φ ≫ cyclicHomParameter n =
      auxiliaryNormalizedCyclicHomPoint g φ := cyclicHomLift_cyclic n _ _

/-- The actual cyclic parameter retains its normalized coefficient morphism. -/
@[reassoc] theorem auxiliaryNormalizedCyclicParameter_base :
    (auxiliaryNormalizedCyclicParameter g p φ).left ≫ (cyclicHomAuxiliaryScheme n).hom =
      T.hom ≫ auxiliaryNormalizedCoefficientBase g :=
  (auxiliaryNormalizedCyclicParameter g p φ).w

end FLT.Mazur.OddWeierstrassParameter
