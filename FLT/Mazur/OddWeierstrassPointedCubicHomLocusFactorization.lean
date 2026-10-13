/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusEquationUniversal
public import FLT.Mazur.OddWeierstrassPointedCubicHomMultiplicationVanishing

/-!
# Odd-chart original pointed cubic parameters factor through the global cyclic locus

The existing original Cartier subgroup forces the multiplication equation.
Its unchanged auxiliary parameter therefore factors through the constructed
global closed locus, also for non-etale cyclic subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve AuxiliaryLevel
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (hφ : H.generatorCurveMarking hP = φ)

/-- The actual original auxiliary cover has a parameter in the global multiplication locus. -/
def pointedCubicHomLocusParameter :
    (pointedCubicAuxiliaryCover W h₃).left ⟶ cyclicHomUniversalMultiplicationLocus n :=
  cyclicHomUniversalLocusLift n (pointedCubicHomAuxiliaryParameter W h₃ φ).left
    (pointedCubicHomMultiplicationEquation_zero W h₃ φ H hP hφ)

/-- The global factorization preserves the full original auxiliary parameter. -/
@[reassoc] theorem pointedCubicHomLocusParameter_inclusion :
    pointedCubicHomLocusParameter W h₃ φ H hP hφ ≫
      cyclicHomUniversalMultiplicationLocusInclusion n =
        (pointedCubicHomAuxiliaryParameter W h₃ φ).left :=
  cyclicHomUniversalLocusLift_inclusion n _ _

/-- Every global lift of the original parameter is the constructed factorization. -/
theorem pointedCubicHomLocusParameter_unique
    (a : (pointedCubicAuxiliaryCover W h₃).left ⟶ cyclicHomUniversalMultiplicationLocus n)
    (ha : a ≫ cyclicHomUniversalMultiplicationLocusInclusion n =
      (pointedCubicHomAuxiliaryParameter W h₃ φ).left) :
    a = pointedCubicHomLocusParameter W h₃ φ H hP hφ :=
  cyclicHomUniversalLocus_lift_unique n _ _
    (ha.trans (pointedCubicHomLocusParameter_inclusion W h₃ φ H hP hφ).symm)

end FLT.Mazur.OddWeierstrassParameter
