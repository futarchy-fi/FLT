/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationSmoothAction
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# The whole modified action on scheme-valued points

The glued action preserves the original coefficient map and commutes with
changing the scheme of points. Its contraction is the original smooth action
on the contracted modified point, with no smoothness assumption on that point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The whole action retains the original smooth parameter's base point. -/
@[reassoc] theorem smoothAction_structure :
    smoothAction W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs =
      pullback.fst (integralSmoothStructure W)
        (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W) ≫
          integralSmoothStructure W := by
  change smoothAction W s b3 b4 b6 h3 h4 h6 hs ≫
    contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W = _
  rw [smoothAction_contraction_assoc]
  exact leftSmoothPointAddition_structure W _ _ _

/-- The actual whole action on any scheme-valued smooth parameter and modified point. -/
def smoothPointAction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs) :
    T ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  pullback.lift a b
    (show a ≫ integralSmoothStructure W =
      b ≫ (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W) from h) ≫
        smoothAction W s b3 b4 b6 h3 h4 h6 hs

/-- Contracting the actual point action gives the original point action. -/
@[reassoc] theorem smoothPointAction_contraction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs) :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs a b h ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      leftSmoothPointAddition W a (b ≫ contraction W s b3 b4 b6 h3 h4 h6 hs)
        (by rw [Category.assoc]; exact h) := by
  rw [smoothPointAction, Category.assoc, smoothAction_contraction]
  change pullback.lift a b
    (show a ≫ integralSmoothStructure W =
      b ≫ (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W) from h) ≫
        leftSmoothPointAddition W _ _ _ = _
  rw [← leftSmoothPointAddition_comp]
  simp only [pullback.lift_fst, pullback.lift_snd_assoc]

/-- The modified point action is a morphism over the original coefficient base. -/
@[reassoc] theorem smoothPointAction_structure {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs) :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs a b h ≫
        structureMap W s b3 b4 b6 h3 h4 h6 hs = a ≫ integralSmoothStructure W := by
  rw [smoothPointAction, Category.assoc, smoothAction_structure, pullback.lift_fst_assoc]

/-- Changing the scheme of points commutes with the constructed entire modified action. -/
theorem smoothPointAction_comp {T U : Scheme.{u}} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs) :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs (p ≫ a) (p ≫ b)
        (by simp only [Category.assoc, h]) =
      p ≫ smoothPointAction W s b3 b4 b6 h3 h4 h6 hs a b h := by
  unfold smoothPointAction
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

end FLT.Mazur.WeierstrassGlobalModification
