/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismAdmissible
public import FLT.Mazur.WeierstrassVariableChangeGroup

/-!
# Every origin-preserving proper cubic isomorphism preserves the group law

Integral classification supplies the actual admissible coordinate change.
Its proved multiplication compatibility upgrades the original isomorphism
itself to an isomorphism of the already constructed group schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- The original base- and origin-preserving isomorphism is an actual group isomorphism. -/
def originIsoGroupIso : integralCurveGroup W hW ≅ integralCurveGroup V hV :=
  CommGrp.mkIso (Over.isoMk e hb)
    (by
      apply Over.OverMorphism.ext
      exact hz)
    (by
      obtain ⟨C, h, he⟩ := originIso_exists_integralVariableChange W V hW hV e hb hz
      subst e
      apply Over.OverMorphism.ext
      change integralCurveAddition W hW ≫ (integralVariableChangeIso V W C h).hom =
        ((integralVariableChangeOverIso V W C h).hom ⊗ₘ
          (integralVariableChangeOverIso V W C h).hom).left ≫ integralCurveAddition V hV
      rw [integralVariableChangeOverIso_tensor]
      exact integralVariableChangeIso_addition V W C h hV hW)

/-- The group upgrade retains the exact given scheme isomorphism in the forward direction. -/
theorem originIsoGroupIso_hom :
    (originIsoGroupIso W V hW hV e hb hz).hom.hom.hom.hom.left = e.hom := rfl

/-- The group upgrade also retains its exact given inverse. -/
theorem originIsoGroupIso_inv :
    (originIsoGroupIso W V hW hV e hb hz).inv.hom.hom.hom.left = e.inv := rfl

end FLT.Mazur.WeierstrassIntegralChart
