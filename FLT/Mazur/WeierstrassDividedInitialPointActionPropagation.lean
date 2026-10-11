/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalStep
public import FLT.Mazur.WeierstrassDividedGlobalPointAction

/-!
# Propagating actual point actions through the retained initial chart

An action equality in the initial model propagates through every finite
successor whenever its input and output lie in the original initial chart.
The proof uses the full unchanged pullback, so the test scheme need not be flat.
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
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "A" => WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- Any coefficient-compatible initial-chart point remains compatible at every stage. -/
theorem globalInitialChart_input_condition {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (x : T ⟶ Spec (.of A))
    (h : a ≫ integralSmoothStructure W = x ≫ c) (j : ℕ) (hj : j ≤ n) :
    a ≫ integralSmoothStructure W =
      (x ≫ globalInitialChart hπ data j hj) ≫ finiteGlobalStructure hπ data j hj := by
  rw [Category.assoc, globalInitialChart_structure]
  exact h

/-- A stage-zero action with retained input and output determines every later actual action. -/
theorem globalInitialChart_pointAction_propagate {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (x y : T ⟶ Spec (.of A))
    (h : a ≫ integralSmoothStructure W = x ≫ c)
    (hzero : finiteGlobalPointAction hπ data 0 (Nat.zero_le n) a
      (x ≫ globalInitialChart hπ data 0 (Nat.zero_le n))
      (globalInitialChart_input_condition hπ data a x h 0 (Nat.zero_le n)) =
        y ≫ globalInitialChart hπ data 0 (Nat.zero_le n))
    (j : ℕ) (hj : j ≤ n) :
    finiteGlobalPointAction hπ data j hj a (x ≫ globalInitialChart hπ data j hj)
      (globalInitialChart_input_condition hπ data a x h j hj) =
        y ≫ globalInitialChart hπ data j hj := by
  induction j with
  | zero => exact hzero
  | succ j ih =>
    apply globalInitialChart_step_lift_unique hπ data j hj y
    rw [finiteGlobalPointAction_step]
    simp only [Category.assoc, globalInitialChart_step]
    exact ih (Nat.le_of_succ_le hj)

end FLT.Mazur.WeierstrassDividedDepth
