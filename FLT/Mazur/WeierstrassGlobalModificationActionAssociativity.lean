/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionInverse

/-!
# Associativity on the whole modification

Inverse translation reduces associativity to uniqueness against a flat third
projection. Naturality removes that flatness restriction on scheme-valued points.
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

/-- Associativity when the third point is a flat reference morphism. -/
theorem smoothPointAction_assoc_of_flat {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (c : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs) [Flat c]
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbc : b ≫ integralSmoothStructure W = c ≫ base) :
    act (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      act a (act b c hbc) (by rw [smoothPointAction_structure]; exact hab) := by
  let d := smoothPairPointAddition W a b hab
  let e := act a (act b c hbc) (by rw [smoothPointAction_structure]; exact hab)
  have hde : d ≫ integralSmoothStructure W = e ≫ base := by
    simp only [d, e, smoothPairPointAddition_structure, smoothPointAction_structure]
  have he : act (d ≫ integralSmoothNegation W) e
      (by rw [Category.assoc, integralSmoothNegation_structure]; exact hde) = c := by
    apply contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs c
    simp only [e, smoothPointAction_contraction]
    have ha := leftSmoothPointAddition_assoc W a b
      (c ≫ contraction W s b3 b4 b6 h3 h4 h6 hs) hab hbc
    simp only [← ha]
    exact leftSmoothPointAddition_neg_cancel W d _ _
  have hh := smoothPointAction_cancel_neg W s b3 b4 b6 h3 h4 h6 hs d e hde
  simpa only [he] using hh

omit [IsDomain R] [IsBezout R] in
/-- Smooth point addition commutes with changing the scheme of points. -/
theorem smoothPairPointAddition_comp {T U : Scheme.{u}} (p : U ⟶ T)
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W) :
    smoothPairPointAddition W (p ≫ a) (p ≫ b)
        (by simp only [Category.assoc, h]) = p ≫ smoothPairPointAddition W a b h := by
  unfold smoothPairPointAddition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- The original smooth sum acts associatively on every point of the whole modification. -/
theorem smoothPointAction_assoc {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (c : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbc : b ≫ integralSmoothStructure W = c ≫ base) :
    act (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      act a (act b c hbc) (by rw [smoothPointAction_structure]; exact hab) := by
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
  let t : T ⟶ pullback pair base := pullback.lift (pullback.lift a b hab) c (by
    change pullback.lift a b hab ≫ pullback.fst f f ≫ f = c ≫ base
    rw [pullback.lift_fst_assoc]
    exact hab.trans hbc)
  have he := congrArg (fun g => t ≫ g)
    (smoothPointAction_assoc_of_flat W s b3 b4 b6 h3 h4 h6 hs x y z hxy hyz)
  simp only [← smoothPointAction_comp, ← smoothPairPointAddition_comp] at he
  simpa only [t, x, y, z, q, pullback.lift_fst_assoc, pullback.lift_fst,
    pullback.lift_snd] using he

end FLT.Mazur.WeierstrassGlobalModification
