/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalInfinityShear
public import FLT.Mazur.WeierstrassVariableChangeZero

/-!
# The original infinity shear is open and retains the origin

The original infinity chart embeds into the sheared chart and contains the
actual cubic zero section. No replacement of the shifted open is made.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
  (r : R) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl

/-- Root shear embeds the whole original infinity chart as an open in the sheared chart. -/
instance nodalInfinityShear_isOpenImmersion :
    IsOpenImmersion (nodalInfinityShear W h₃ h₄ h₆ r hr) := by
  have : IsOpenImmersion
      (nodalInfinityShear W h₃ h₄ h₆ r hr ≫ integralCurveChart U 1) := by
    rw [nodalInfinityShear_global]
    infer_instance
  exact IsOpenImmersion.of_comp _ (integralCurveChart U 1)

/-- The entire original zero section survives in the shifted infinity open. -/
@[reassoc] theorem nodalInfinityShear_zero :
    Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) ≫
        nodalInfinityShear W h₃ h₄ h₆ r hr =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) U).toRingHom) := by
  apply (cancel_mono (integralCurveChart U 1)).mp
  rw [Category.assoc, nodalInfinityShear_global, ← Category.assoc]
  change integralCurveZero W ≫ (i).inv = integralCurveZero U
  apply (cancel_mono (i).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, integralVariableChangeIso_zero]

end FLT.Mazur.WeierstrassIntegralChart
