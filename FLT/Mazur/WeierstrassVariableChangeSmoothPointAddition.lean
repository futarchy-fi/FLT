/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothAddition
public import FLT.Mazur.WeierstrassLeftSmoothPointAssociativity

/-!
# Variable changes preserve smooth addition on every test scheme

The full smooth addition square specializes to arbitrary pairs of points.
No flatness or reducedness condition is imposed on the test scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "e" => integralVariableChangeSmoothMap W V C h

/-- The two changed smooth inputs have the same original coefficient map. -/
theorem integralVariableChangeSmoothPair_condition {T : Scheme}
    (p q : T ⟶ (integralSmoothOpen V).toScheme)
    (hpq : p ≫ integralSmoothStructure V = q ≫ integralSmoothStructure V) :
    (p ≫ e) ≫ integralSmoothStructure W = (q ≫ e) ≫ integralSmoothStructure W := by
  simpa only [Category.assoc, integralVariableChangeSmoothMap_structure] using hpq

/-- The actual pointwise smooth sum commutes with every integral variable change. -/
@[reassoc] theorem integralVariableChangeSmoothMap_pointAddition {T : Scheme}
    (p q : T ⟶ (integralSmoothOpen V).toScheme)
    (hpq : p ≫ integralSmoothStructure V = q ≫ integralSmoothStructure V) :
    smoothPairPointAddition V p q hpq ≫ e =
      smoothPairPointAddition W (p ≫ e) (q ≫ e)
        (integralVariableChangeSmoothPair_condition W V C h p q hpq) := by
  have hp : pullback.lift p q hpq ≫ integralVariableChangeSmoothProduct W V C h =
      pullback.lift (p ≫ e) (q ≫ e)
        (integralVariableChangeSmoothPair_condition W V C h p q hpq) := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, integralVariableChangeSmoothProduct_fst,
        integralVariableChangeSmoothProduct_snd, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [smoothPairPointAddition, Category.assoc, integralVariableChangeSmoothMap_addition,
    ← Category.assoc, hp]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
