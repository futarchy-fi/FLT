/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeAddition
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# Admissible changes are isomorphisms of the original group schemes

Both group objects use their already constructed global operations. The
unit and multiplication compatibilities are proved for the actual proper
coordinate change, so the bundled isomorphism carries no assumed group law.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The categorical tensor of the proper change is the actual product morphism. -/
theorem integralVariableChangeOverIso_tensor :
    ((integralVariableChangeOverIso W V C h).hom ⊗ₘ
      (integralVariableChangeOverIso W V C h).hom).left =
        integralVariableChangeProduct W V C h := by
  apply pullback.hom_ext
  · exact (Over.tensorHom_left_fst (integralCurveStructure W) (integralCurveStructure W)
      (integralVariableChangeOverIso W V C h).hom
      (integralVariableChangeOverIso W V C h).hom).trans
        (integralVariableChangeProduct_fst W V C h).symm
  · exact (Over.tensorHom_left_snd (integralCurveStructure W) (integralCurveStructure W)
      (integralVariableChangeOverIso W V C h).hom
      (integralVariableChangeOverIso W V C h).hom).trans
        (integralVariableChangeProduct_snd W V C h).symm

/-- The actual admissible proper isomorphism is an isomorphism of commutative group schemes. -/
def integralVariableChangeGroupIso (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    integralCurveGroup V hV ≅ integralCurveGroup W hW :=
  CommGrp.mkIso (integralVariableChangeOverIso W V C h)
    (by
      apply Over.OverMorphism.ext
      exact integralVariableChangeIso_zero W V C h)
    (by
      apply Over.OverMorphism.ext
      change integralCurveAddition V hV ≫ (integralVariableChangeIso W V C h).hom =
        ((integralVariableChangeOverIso W V C h).hom ⊗ₘ
          (integralVariableChangeOverIso W V C h).hom).left ≫ integralCurveAddition W hW
      rw [integralVariableChangeOverIso_tensor]
      exact integralVariableChangeIso_addition W V C h hW hV)

/-- Forgetting the group structure recovers the exact original proper map. -/
theorem integralVariableChangeGroupIso_hom (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    (integralVariableChangeGroupIso W V C h hW hV).hom.hom.hom.hom.left =
      (integralVariableChangeIso W V C h).hom := rfl

/-- The inverse group isomorphism is the exact original inverse proper map. -/
theorem integralVariableChangeGroupIso_inv (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    (integralVariableChangeGroupIso W V C h hW hV).inv.hom.hom.hom.left =
      (integralVariableChangeIso W V C h).inv := rfl

end FLT.Mazur.WeierstrassIntegralChart
