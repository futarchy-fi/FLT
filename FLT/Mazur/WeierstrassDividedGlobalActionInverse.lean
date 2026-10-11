/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionIdentity

/-!
# Inverse translations at every finite depth

At each successor, flat-reference uniqueness proves inverse cancellation
on the universal product. Naturality transports it to all scheme-valued
points, including exceptional and nonflat inputs.
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

/-- The negative smooth parameter undoes the action at every finite depth. -/
theorem finiteGlobalPointAction_neg_cancel (j : ℕ) (hj : j ≤ n) {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ finiteGlobalStructure hπ data j hj) :
    finiteGlobalPointAction hπ data j hj (a ≫ integralSmoothNegation W)
      (finiteGlobalPointAction hπ data j hj a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        finiteGlobalPointAction_structure]) = b := by
  induction j generalizing T with
  | zero =>
    simp only [finiteGlobalPointAction_zero_stage]
    exact finiteGlobalInitialPointAction_neg_cancel hπ data a b h
  | succ j ih =>
    let base := finiteGlobalStructure hπ data (j + 1) hj
    let x := pullback.fst (integralSmoothStructure W) base
    let z := pullback.snd (integralSmoothStructure W) base
    have hxz : x ≫ integralSmoothStructure W = z ≫ base := pullback.condition
    have hz : Flat z := by dsimp [z]; infer_instance
    let _ := hz
    have he : finiteGlobalPointAction hπ data (j + 1) hj (x ≫ integralSmoothNegation W)
        (finiteGlobalPointAction hπ data (j + 1) hj x z hxz)
        (by rw [Category.assoc, integralSmoothNegation_structure,
          finiteGlobalPointAction_structure]) = z := by
      apply finiteGlobalStep_ext_of_flat hπ data j hj z
      simp only [finiteGlobalPointAction_step]
      exact ih (Nat.le_of_succ_le hj) x (z ≫ finiteGlobalStep hπ data j hj) _
    let p := pullback.lift a b h
    have hh := congrArg (fun f => p ≫ f) he
    simp only [← finiteGlobalPointAction_comp] at hh
    simpa only [p, x, z, base, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd] using hh

/-- Translation also undoes the action of the negative parameter at every finite depth. -/
theorem finiteGlobalPointAction_cancel_neg (j : ℕ) (hj : j ≤ n) {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ finiteGlobalStructure hπ data j hj) :
    finiteGlobalPointAction hπ data j hj a
      (finiteGlobalPointAction hπ data j hj (a ≫ integralSmoothNegation W) b
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact h))
      (by rw [finiteGlobalPointAction_structure, Category.assoc,
        integralSmoothNegation_structure]) = b := by
  have he := finiteGlobalPointAction_neg_cancel hπ data j hj
    (a ≫ integralSmoothNegation W) b
    (by rw [Category.assoc, integralSmoothNegation_structure]; exact h)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using he

end FLT.Mazur.WeierstrassDividedDepth
