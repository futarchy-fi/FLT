/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionIdentity

/-!
# Inverse translations on the entire modification

Flat-reference uniqueness proves cancellation on the universal product.
Pullback naturality then gives cancellation for arbitrary scheme-valued points,
including exceptional points; their maps need not be flat.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

local notation "act" => smoothPointAction W s b3 b4 b6 h3 h4 h6 hs
local notation "base" => structureMap W s b3 b4 b6 h3 h4 h6 hs
local notation "fst" => pullback.fst (integralSmoothStructure W) base
local notation "snd" => pullback.snd (integralSmoothStructure W) base

/-- The negative parameter undoes the universal action, including exceptional inputs. -/
theorem smoothPointAction_neg_cancel_projections :
    act (fst ≫ integralSmoothNegation W) (act fst snd pullback.condition)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        smoothPointAction_structure]) = snd := by
  apply contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs snd
  simp only [smoothPointAction_contraction]
  exact leftSmoothPointAddition_neg_cancel W fst _ _

/-- The actual negative translation undoes the action on every scheme-valued point. -/
theorem smoothPointAction_neg_cancel {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    act (a ≫ integralSmoothNegation W) (act a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        smoothPointAction_structure]) = b := by
  let p := pullback.lift a b h
  have he := congrArg (fun f => p ≫ f)
    (smoothPointAction_neg_cancel_projections W s b3 b4 b6 h3 h4 h6 hs)
  simp only [← smoothPointAction_comp] at he
  simpa only [p, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd] using he

/-- Translation also undoes the action by the negative parameter on every modified point. -/
theorem smoothPointAction_cancel_neg {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    act a (act (a ≫ integralSmoothNegation W) b
      (by rw [Category.assoc, integralSmoothNegation_structure]; exact h))
      (by rw [smoothPointAction_structure, Category.assoc,
        integralSmoothNegation_structure]) = b := by
  have he := smoothPointAction_neg_cancel W s b3 b4 b6 h3 h4 h6 hs
    (a ≫ integralSmoothNegation W) b
    (by rw [Category.assoc, integralSmoothNegation_structure]; exact h)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using he

end FLT.Mazur.WeierstrassGlobalModification
