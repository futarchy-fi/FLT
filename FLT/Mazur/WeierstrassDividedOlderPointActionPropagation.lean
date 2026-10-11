/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalStep
public import FLT.Mazur.WeierstrassDividedGlobalPointAction

/-!
# Propagating point actions on the original older successive charts

An action computed where the successive chart first appears determines its
actual action at every later stage. The input and output remain in the same
integral equation chart throughout, without a shifted-model identification.
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
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- Original coefficient-compatible points stay compatible through all later retention. -/
theorem olderGlobalChart_input_condition {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (x : T ⟶ stepX e)
    (h : a ≫ integralSmoothStructure W = x ≫ c) (r : ℕ) (hr : j + 1 + r ≤ n) :
    a ≫ integralSmoothStructure W =
      (x ≫ olderGlobalChart hπ data j hj r hr) ≫
        finiteGlobalStructure hπ data (j + 1 + r) hr := by
  rw [Category.assoc, olderGlobalChart_structure]
  exact h

/-- A computed action on the first appearance of a chart determines every retained action. -/
theorem olderGlobalChart_pointAction_propagate {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (x y : T ⟶ stepX e)
    (h : a ≫ integralSmoothStructure W = x ≫ c)
    (hzero : finiteGlobalPointAction hπ data (j + 1) hj a
      (x ≫ olderGlobalChart hπ data j hj 0 hj)
      (olderGlobalChart_input_condition hπ data j hj a x h 0 hj) =
        y ≫ olderGlobalChart hπ data j hj 0 hj)
    (r : ℕ) (hr : j + 1 + r ≤ n) :
    finiteGlobalPointAction hπ data (j + 1 + r) hr a
      (x ≫ olderGlobalChart hπ data j hj r hr)
      (olderGlobalChart_input_condition hπ data j hj a x h r hr) =
        y ≫ olderGlobalChart hπ data j hj r hr := by
  induction r with
  | zero => exact hzero
  | succ r ih =>
    apply olderGlobalChart_step_lift_unique hπ data j hj r hr y
    erw [finiteGlobalPointAction_step hπ data (j + 1 + r)]
    simp only [Category.assoc, olderGlobalChart_step]
    exact ih (by omega)

end FLT.Mazur.WeierstrassDividedDepth
