/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalProjectiveReflection
public import FLT.Mazur.WeierstrassVariableChangeProjectiveComposition
public import FLT.Mazur.WeierstrassRootShearSmoothParameter

/-!
# The actual root-sheared smooth parameters differ by Laurent inversion

Both maps use their independently constructed proper-cubic variable changes.
The comparison holds on the full torus over any coefficient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (r : R) (a : Rˣ)
  (ha : (a : R) = W.a₁ + 2 * r)
  (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
local notation "s" => (-W.a₁ - r)
local notation "C" => (VariableChange.mk 1 0 r 0 : VariableChange R)
local notation "D" => (VariableChange.mk 1 0 s 0 : VariableChange R)
local notation "E" => (VariableChange.mk 1 0 (-(a : R)) 0 : VariableChange R)
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := R)).toRingHom)

include ha in
/-- The opposite root has the negative tangent unit over the same coefficient ring. -/
theorem rootShearOpposite_tangent : ((-a : Rˣ) : R) = W.a₁ + 2 * s := by
  rw [Units.val_neg, ha]
  ring

include hr in
/-- The other ordered tangent is itself a root of the original tangent equation. -/
theorem rootShearOpposite_root : s ^ 2 + W.a₁ * s - W.a₂ = 0 := by
  linear_combination hr

include ha in
/-- The actual shear to the opposite root factors through the split signed shear. -/
theorem rootShearOpposite_change : E * C = D := by
  ext <;> simp [VariableChange.mul_def, ha]; ring

local notation "hs" => rootShearOpposite_root W r hr
local notation "hb" => rootShearOpposite_tangent W r a ha
local notation "Ir" => rootShearTorusSmoothIso W r a ha hr h3 h4 h6
local notation "Is" => rootShearTorusSmoothIso W s (-a) hb hs h3 h4 h6

/-- Laurent inversion identifies both full original smooth parameter maps. -/
@[reassoc] theorem rootShearTorusSmoothIso_reflection : ι ≫ (Is).hom = (Ir).hom := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, rootShearTorusSmoothIso_inclusion, rootShearTorusSmoothIso_inclusion]
  apply (cancel_mono (integralProjectiveMap W)).mp
  change (ι ≫ splitNodalTorusToCurve (-a) ≫ integralVariableChangeTo W _ D _) ≫ _ =
    (splitNodalTorusToCurve a ≫ integralVariableChangeTo W _ C _) ≫ _
  simp only [Category.assoc, integralVariableChangeTo_projectiveMap]
  rw [← rootShearOpposite_change W r a ha, integralVariableChangeProjective_mul, Iso.trans_hom]
  have H := congrArg (fun f => f ≫ (WeierstrassVariableChangeLinear.projectiveIso C).hom)
    (splitNodalTorus_projectiveReflection a)
  simpa only [Category.assoc] using H

/-- The actual comparison is the explicit inverse Laurent map, including the origin. -/
theorem rootShearTorusParameter_reflection : (Ir).hom ≫ (Is).inv = ι := by
  rw [← rootShearTorusSmoothIso_reflection W r a ha hr h3 h4 h6,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
