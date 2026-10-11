/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionConstruction

/-!
# Scheme-valued points of every finite global action

The whole action maps induce natural point operations. They preserve
coefficients, original smooth addition, and every successor contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj

/-- Apply the constructed whole action to any pair over the original coefficient scheme. -/
def finiteGlobalPointAction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    T ⟶ finiteGlobalModel hπ data j hj :=
  pullback.lift a b h ≫ finiteGlobalAction hπ data j hj

/-- Point actions preserve the smooth parameter's coefficient morphism. -/
@[reassoc] theorem finiteGlobalPointAction_structure {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalPointAction hπ data j hj a b h ≫ base =
      a ≫ integralSmoothStructure W := by
  rw [finiteGlobalPointAction, Category.assoc, finiteGlobalAction_structure,
    pullback.lift_fst_assoc]

/-- Point actions contract to genuine smooth addition on the original entire cubic. -/
@[reassoc] theorem finiteGlobalPointAction_contraction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalPointAction hπ data j hj a b h ≫ finiteGlobalContraction hπ data j hj =
      leftSmoothPointAddition W a (b ≫ finiteGlobalContraction hπ data j hj) h := by
  rw [finiteGlobalPointAction, Category.assoc, finiteGlobalAction_contraction]
  unfold leftSmoothPointAddition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, finiteGlobalActionInput_fst, finiteGlobalActionInput_snd,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The point operation is natural for arbitrary changes of the scheme of points. -/
theorem finiteGlobalPointAction_comp {T U : Scheme.{u}} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalPointAction hπ data j hj (p ≫ a) (p ≫ b)
        (by simp only [Category.assoc, h]) =
      p ≫ finiteGlobalPointAction hπ data j hj a b h := by
  unfold finiteGlobalPointAction
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

omit hj in
/-- Every successor point action contracts to the preceding point action. -/
@[reassoc] theorem finiteGlobalPointAction_step (hnext : j + 1 ≤ n) {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hnext)
    (h : a ≫ integralSmoothStructure W = b ≫ finiteGlobalStructure hπ data (j + 1) hnext) :
    finiteGlobalPointAction hπ data (j + 1) hnext a b h ≫ finiteGlobalStep hπ data j hnext =
      finiteGlobalPointAction hπ data j (Nat.le_of_succ_le hnext) a
        (b ≫ finiteGlobalStep hπ data j hnext)
        (by rw [Category.assoc, finiteGlobalStep_structure]; exact h) := by
  rw [finiteGlobalPointAction, Category.assoc, finiteGlobalAction_step]
  unfold finiteGlobalPointAction
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, successorActionInput_fst, successorActionInput_snd,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end FLT.Mazur.WeierstrassDividedDepth
