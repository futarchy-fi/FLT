/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionInverse

/-!
# Associativity on every finite global model

Successor-step uniqueness and inverse cancellation prove the action law
on a universal flat product. Naturality includes all scheme-valued points.
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

/-- Original smooth addition acts associatively on every finite global model. -/
theorem finiteGlobalPointAction_assoc (j : ℕ) (hj : j ≤ n) {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (c : T ⟶ finiteGlobalModel hπ data j hj)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbc : b ≫ integralSmoothStructure W = c ≫ finiteGlobalStructure hπ data j hj) :
    finiteGlobalPointAction hπ data j hj (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      finiteGlobalPointAction hπ data j hj a (finiteGlobalPointAction hπ data j hj b c hbc)
        (by rw [finiteGlobalPointAction_structure]; exact hab) := by
  induction j generalizing T with
  | zero =>
    simp only [finiteGlobalPointAction_zero_stage]
    exact finiteGlobalInitialPointAction_assoc hπ data a b c hab hbc
  | succ j ih =>
    let base := finiteGlobalStructure hπ data (j + 1) hj
    let f := integralSmoothStructure W
    let pair := pullback.fst f f ≫ f
    let q := pullback.fst pair base
    let z := pullback.snd pair base
    let x := q ≫ pullback.fst f f
    let y := q ≫ pullback.snd f f
    have hxy : x ≫ f = y ≫ f := by
      simp only [x, y, Category.assoc, pullback.condition]
    have hyz : y ≫ f = z ≫ base := by
      rw [← hxy]
      exact pullback.condition (f := pair) (g := base)
    have hflat : Flat z := by dsimp [z, pair, f]; infer_instance
    let _ := hflat
    let d := smoothPairPointAddition W x y hxy
    let e := finiteGlobalPointAction hπ data (j + 1) hj x
      (finiteGlobalPointAction hπ data (j + 1) hj y z hyz)
      (by rw [finiteGlobalPointAction_structure]; exact hxy)
    have hde : d ≫ integralSmoothStructure W = e ≫ base := by
      simp only [d, e, base, smoothPairPointAddition_structure, finiteGlobalPointAction_structure]
    have he : finiteGlobalPointAction hπ data (j + 1) hj
        (d ≫ integralSmoothNegation W) e
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact hde) = z := by
      apply finiteGlobalStep_ext_of_flat hπ data j hj z
      simp only [e, finiteGlobalPointAction_step]
      have ha := ih (Nat.le_of_succ_le hj) x y
        (z ≫ finiteGlobalStep hπ data j hj) hxy
        (by simpa only [Category.assoc, finiteGlobalStep_structure] using hyz)
      simp only [← ha]
      exact finiteGlobalPointAction_neg_cancel hπ data j (Nat.le_of_succ_le hj) d _ _
    have hh := finiteGlobalPointAction_cancel_neg hπ data (j + 1) hj d e hde
    simp only [he] at hh
    let t : T ⟶ pullback pair base := pullback.lift (pullback.lift a b hab) c (by
      change pullback.lift a b hab ≫ pullback.fst f f ≫ f = c ≫ base
      rw [pullback.lift_fst_assoc]
      exact hab.trans hbc)
    have ht := congrArg (fun g => t ≫ g) hh
    dsimp only [d, e] at ht
    simp only [← finiteGlobalPointAction_comp,
      ← WeierstrassGlobalModification.smoothPairPointAddition_comp] at ht
    simpa only [t, x, y, z, q, base, pullback.lift_fst_assoc, pullback.lift_fst,
      pullback.lift_snd] using ht

end FLT.Mazur.WeierstrassDividedDepth
