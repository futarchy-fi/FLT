/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothWholeAction
public import FLT.Mazur.WeierstrassSmoothGroupEquationTransport

/-!
# Equation transport of the full smooth-by-whole action

Transport of a Weierstrass equation preserves its whole-curve action, including
singular inputs. The curve transport is sealed to keep coefficient proofs small.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {U V : WeierstrassCurve R}

/-- Sealed transport of the entire relative cubic along equality of equations. -/
irreducible_def equationCurveOverIso (h : U = V) :
    integralCurveOver U ≅ integralCurveOver V :=
  eqToIso (congrArg integralCurveOver h)

/-- The relative transport retains the literal transport of the whole schemes. -/
theorem equationCurveOverIso_hom_left (h : U = V) :
    (equationCurveOverIso h).hom.left = eqToHom (congrArg integralCurve h) := by
  rw [equationCurveOverIso_def]
  subst V
  rfl

/-- Equation transport identifies the actual actions on the entire cubics. -/
theorem equationCurveOverIso_action (h : U = V) :
    integralSmoothWholeAction U ≫ (equationCurveOverIso h).hom =
      (((CommGrp.forget (Over (Spec (.of R)))).mapIso
        (smoothEquationGroupIso h)).hom ⊗ₘ (equationCurveOverIso h).hom) ≫
          integralSmoothWholeAction V := by
  subst V
  rw [equationCurveOverIso_def, smoothEquationGroupIso_def]
  simp

end FLT.Mazur.WeierstrassIntegralChart
