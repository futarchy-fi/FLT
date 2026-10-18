/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingRelativeGroupSpecialization
public import FLT.Mazur.OneGonSmoothingClosedFiber

/-!
# Smooth and whole-curve equation transports in the one-gon coefficient comparison

Equation transport commutes with the actual smooth inclusion. The zero-parameter
fiber comparison uses exactly the same transport on the whole coefficient cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Equation transport on the smooth group commutes with its original open immersion. -/
@[reassoc] theorem equationGroupTransport_inclusion {R : Type} [CommRing R]
    {U V : WeierstrassCurve R} (h : U = V) :
    (eqToIso (congrArg integralSmoothGroup h)).hom.hom.hom.hom.left ≫
      (integralSmoothOpen V).ι =
        (integralSmoothOpen U).ι ≫ eqToHom (congrArg integralCurve h) := by
  subst V
  simp

/-- Inverse equation transport also retains the original smooth inclusion. -/
@[reassoc] theorem equationGroupTransport_inv_inclusion {R : Type} [CommRing R]
    {U V : WeierstrassCurve R} (h : U = V) :
    (eqToIso (congrArg integralSmoothGroup h)).inv.hom.hom.hom.left ≫
      (integralSmoothOpen U).ι =
        (integralSmoothOpen V).ι ≫ eqToHom (congrArg integralCurve h.symm) := by
  subst V
  simp

/-- Zero-parameter transport retains the same full coefficient morphism. -/
theorem zeroParameterFiberIso_equation_fst {R : Type} [CommRing R]
    (K : Type) [Field K] [Algebra R K] (t : R) (ht : algebraMap R K t = 0) :
    (zeroParameterFiberIso K t ht).hom ≫
      pullback.fst (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
    (zeroFiberIso K).hom ≫
      eqToHom (congrArg integralCurve
        ((equation_map t (algebraMap R K)).trans (congrArg equation ht)).symm) ≫
        integralCoefficientMorphism (S := K) (equation t) := by
  rw [zeroParameterFiberIso_fst, coefficientMorphism]
  simp only [← Category.assoc, eqToHom_trans]

end FLT.Mazur.OneGonSmoothing
