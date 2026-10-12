/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationFunctionDescent

/-!
# The full two-endpoint restriction of a scheme relation

Both source coordinates are pulled back independently. The universal lift retains
the original relation arrow, so compatibility tests every arrow on the restriction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A X Y : Scheme.{u}} (p q : A ⟶ X) (k : Y ⟶ X)

/-- Original arrows with their first endpoint lifted to the new source. -/
def firstDomain : Scheme.{u} := pullback p k

/-- Original arrows with both endpoints lifted independently to the new source. -/
def doubleDomain : Scheme.{u} := pullback (pullback.fst p k ≫ q) k

/-- The original arrow of the double restriction. -/
def arrow : doubleDomain p q k ⟶ A :=
  pullback.fst (pullback.fst p k ≫ q) k ≫ pullback.fst p k

/-- The first endpoint in the restricted source. -/
def fst : doubleDomain p q k ⟶ Y :=
  pullback.fst (pullback.fst p k ≫ q) k ≫ pullback.snd p k

/-- The independent second endpoint in the restricted source. -/
def snd : doubleDomain p q k ⟶ Y := pullback.snd (pullback.fst p k ≫ q) k

@[reassoc]
theorem arrow_fst : arrow p q k ≫ p = fst p q k ≫ k := by
  simp only [arrow, fst, Category.assoc, pullback.condition]

@[reassoc]
theorem arrow_snd : arrow p q k ≫ q = snd p q k ≫ k := by
  exact (Category.assoc _ _ _).trans (pullback.condition (f := pullback.fst p k ≫ q))

variable {T : Scheme.{u}} (a : T ⟶ A) (x y : T ⟶ Y)
  (hx : a ≫ p = x ≫ k) (hy : a ≫ q = y ≫ k)

/-- Lift an unchanged original arrow together with its two source lifts. -/
def lift : T ⟶ doubleDomain p q k :=
  pullback.lift (pullback.lift a x hx) y (by rw [pullback.lift_fst_assoc, hy])

@[reassoc]
theorem lift_arrow : lift p q k a x y hx hy ≫ arrow p q k = a := by
  simp only [lift, arrow, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc]
theorem lift_fst : lift p q k a x y hx hy ≫ fst p q k = x := by
  simp only [lift, fst, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem lift_snd : lift p q k a x y hx hy ≫ snd p q k = y :=
  pullback.lift_snd _ _ _

include a hx hy in
/-- Compatibility on the full restriction tests every original arrow with lifted endpoints. -/
theorem compatible_on_arrow
    (s : SchemeEffectiveEpiSections.compatibleFunctions (fst p q k) (snd p q k)) :
    x.appTop s.val = y.appTop s.val := by
  have h := congrArg (lift p q k a x y hx hy).appTop s.property
  change ((lift p q k a x y hx hy ≫ fst p q k).appTop s.val) =
    ((lift p q k a x y hx hy ≫ snd p q k).appTop s.val) at h
  simpa only [lift_fst, lift_snd] using h

end FLT.Mazur.SchemeRelationRestriction
