/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearSmoothParameter
public import FLT.Mazur.WeierstrassVariableChangeIdentity
public import FLT.Mazur.WeierstrassInfinityResidueSmooth

/-!
# The zero-root torus parameter retains the original split equation

The actual proper variable change is the identity for the zero root.
Consequently the root-sheared torus has the original positive Laurent orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- The identity variable change fixes the full smooth open, including singular fibers. -/
theorem integralVariableChangeSmoothMap_one (W : WeierstrassCurve R) :
    integralVariableChangeSmoothMap W W 1 (one_smul _ _) =
      𝟙 (integralSmoothOpen W).toScheme := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [integralVariableChangeSmoothMap_inclusion, integralVariableChangeIso_one]
  simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The zero-root smooth torus is exactly the original equation-transport torus. -/
theorem rootShearTorusSmoothIso_zero (W : WeierstrassCurve R) (a : Rˣ)
    (h : W = splitNodalEquation a)
    (ha : (a : R) = W.a₁ + 2 * 0) (hr : 0 ^ 2 + W.a₁ * 0 - W.a₂ = 0)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    rootShearTorusSmoothIso W 0 a ha hr h3 h4 h6 = splitEquationSmoothIso a h := by
  subst W
  apply Iso.ext
  change (splitNodalRelativeSmoothIso a).hom ≫
    integralVariableChangeSmoothMap _ _ 1 _ = _
  rw [integralVariableChangeSmoothMap_one, Category.comp_id]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
