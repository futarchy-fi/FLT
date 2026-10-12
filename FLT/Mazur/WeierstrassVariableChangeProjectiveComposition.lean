/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralIso

/-!
# Composition of actual projective and proper cubic variable changes

The ambient linear construction and the original closed cubic embedding
identify the complete composite, over every coefficient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassVariableChangeLinear
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- Multiplication of admissible changes retains the full linear equivalence. -/
theorem integralVariableChangeLinear_mul (C D : VariableChange R) :
    linearEquiv (C * D) = (linearEquiv D).trans (linearEquiv C) := by
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_mul C D

/-- Actual ambient projective maps compose in the order of coordinate substitution. -/
theorem integralVariableChangeProjective_mul (C D : VariableChange R) :
    projectiveIso (C * D) = projectiveIso C ≪≫ projectiveIso D := by
  rw [projectiveIso, integralVariableChangeLinear_mul]
  change ProjectiveSpace.linearIso ((linearEquiv C).symm.trans (linearEquiv D).symm) = _
  exact (ProjectiveSpace.linearIso_trans (linearEquiv C).symm (linearEquiv D).symm).symm

/-- The entire proper-cubic coordinate change agrees with the composite of both changes. -/
@[reassoc] theorem integralVariableChangeTo_comp
    (W V U : WeierstrassCurve R) (C D : VariableChange R)
    (hC : C • V = U) (hD : D • W = V) (hCD : (C * D) • W = U) :
    integralVariableChangeTo V U C hC ≫ integralVariableChangeTo W V D hD =
      integralVariableChangeTo W U (C * D) hCD := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    integralVariableChangeTo_projectiveMap_assoc, integralVariableChangeTo_projectiveMap,
    integralVariableChangeProjective_mul, Iso.trans_hom]

end FLT.Mazur.WeierstrassIntegralChart
