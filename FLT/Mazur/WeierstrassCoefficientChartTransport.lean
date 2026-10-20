/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientRingMap
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso

/-!
# Coefficient chart maps with an identified target equation

Transport of an equation preserves the original smooth inclusion. The
coefficient map on normalized chart rings is the restriction of the actual
coefficient morphism on the whole cubic, also after identifying the equation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Equation transport retains the original open immersion of the smooth group. -/
@[reassoc] theorem equationTransport_smoothInclusion {U V : WeierstrassCurve S} (h : U = V) :
    (eqToHom (congrArg integralSmoothGroup h)).hom.hom.hom.left ≫
      (integralSmoothOpen V).ι =
        (integralSmoothOpen U).ι ≫ eqToHom (congrArg integralCurve h) := by
  subst V
  simp

variable (f : R →+* S) (W : WeierstrassCurve R) (j : Fin 3)
  (V : WeierstrassCurve S) (h : W.map f = V)

/-- The transported chart ring map gives the actual original cubic coefficient square. -/
theorem chartCoefficientRingMapTo_inclusion :
    Spec.map (CommRingCat.ofHom (chartCoefficientRingMapTo f W j V h)) ≫
      integralCurveChart W j =
        integralCurveChart V j ≫ eqToHom (congrArg integralCurve h.symm) ≫
          @integralCoefficientMorphism R S _ _ f.toAlgebra W := by
  subst V
  simpa only [chartCoefficientRingMapTo, chartCoefficientRingMap, chartCoefficientMorphism,
    eqToHom_refl, Category.id_comp, RingHom.algebraMap_toAlgebra] using
    (@integralCurveChart_coefficientMorphism R S _ _ f.toAlgebra W j).symm

end FLT.Mazur.WeierstrassIntegralChart
