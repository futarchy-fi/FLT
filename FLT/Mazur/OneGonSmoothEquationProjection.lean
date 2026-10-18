/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCoefficientTransport

/-!
# The geometric inverse of a nodal coefficient group comparison

The nodal group inverse retains the original Laurent parametrization. Abstract
equation transport and group-composition projections supply smaller identities
for the comparison with the particular complete cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Group equation transport induces the actual equation transport on smooth schemes. -/
theorem equationGroupTransport_inv_left {R : Type} [CommRing R]
    {U V : WeierstrassCurve R} (h : U = V) :
    (eqToIso (congrArg integralSmoothGroup h)).inv.hom.hom.hom.left =
      eqToHom (congrArg (fun W => (integralSmoothOpen W).toScheme) h.symm) := by
  subst V
  rfl

/-- Smooth equation transport commutes with the original open immersion. -/
@[reassoc] theorem smoothEquationTransport_inclusion {R : Type} [CommRing R]
    {U V : WeierstrassCurve R} (h : U = V) :
    eqToHom (congrArg (fun W => (integralSmoothOpen W).toScheme) h) ≫
      (integralSmoothOpen V).ι =
        (integralSmoothOpen U).ι ≫ eqToHom (congrArg integralCurve h) := by
  subst V
  simp

/-- The inverse full nodal group comparison retains the original smooth parametrization. -/
theorem nodalGroupIso_inv {R : Type} [CommRing R] (a : Rˣ) :
    (integralSmoothSplitNodalTorusIso a).inv.hom.hom.hom =
      (splitNodalRelativeSmoothOverIso a).hom := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Forgetting an inverse composite retains its three geometric factors. -/
theorem groupIsoTriple_inv_left {S : Scheme}
    {A B C D : CommGrp (Over S)} (a : A ≅ B) (b : B ≅ C) (c : C ≅ D) :
    (a ≪≫ b ≪≫ c).inv.hom.hom.hom.left =
      (c.inv.hom.hom.hom.left ≫ b.inv.hom.hom.hom.left) ≫ a.inv.hom.hom.hom.left := rfl

end FLT.Mazur.OneGonSmoothing
