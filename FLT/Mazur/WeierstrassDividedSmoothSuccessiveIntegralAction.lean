/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderCubicAction

/-!
# The actual finite interior action on the common integral refinement

The original cubic action square and proved regular output x identify the
constructed integral output with the actual finite-model point action. The
same equality holds at every retained stage and after arbitrary specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "L" => SmoothSuccessiveActionOpen e hπ
local notation "c" => olderGlobalChart hπ data j hj r hr
local notation "a" => smoothSuccessiveIntegralPoint e hπ
local notation "f" => smoothSuccessiveIntegralInput e hπ
local notation "g" => smoothSuccessiveIntegralOutput e hπ
local notation "ha" => smoothSuccessiveIntegralPoint_structure e hπ
local notation "h" => olderGlobalChart_algebra_condition hπ data j hj r hr a f ha

/-- The genuine integral output is the actual point action in the original finite model. -/
theorem smoothSuccessiveIntegral_finitePointAction :
    finiteGlobalPointAction hπ data (j + 1 + r) hr a
      (Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c) h =
        Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ c :=
  olderGlobalChart_pointAction_of_cubic hπ data j hj r hr a f g ha
    (smoothSuccessiveIntegralOutput_cubic_x_regular e hπ)
    (smoothSuccessiveIntegralOutput_cubic_addition e hπ)

/-- Specializing the proved integral action requires no flatness of the specialization. -/
theorem smoothSuccessiveIntegral_finitePointAction_specialize {U : Scheme.{u}}
    (z : U ⟶ Spec (.of L)) :
    finiteGlobalPointAction hπ data (j + 1 + r) hr (z ≫ a)
      (z ≫ Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c)
      (by simpa only [Category.assoc] using congrArg (z ≫ ·) h) =
        z ≫ Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ c := by
  exact (finiteGlobalPointAction_comp hπ data (j + 1 + r) hr z a
    (Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c) h).trans
      (congrArg (z ≫ ·) (smoothSuccessiveIntegral_finitePointAction hπ data j hj r hr))

end FLT.Mazur.WeierstrassDividedDepth
