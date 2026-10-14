/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedEffective

/-!
# Full original kernels on selections inside a propagated monic seed

Any scheme mapping into the propagated source inherits its full kernel
criterion. Both endpoints are restricted independently, and the original
relation arrow is constructed by division. This applies to actual affine
open selections, without assuming that they are saturated in the source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z C : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
variable (k : C ⟶ A.left) (t : C ⟶ pullback q.left a)
  (hk : t ≫ SchemeRelationEtaleBranchPropagation.branch p.left q.left a = k)
local notation "p'" => SchemeRelationRestriction.fst p.left q.left k
local notation "q'" => SchemeRelationRestriction.snd p.left q.left k
local notation "r" => SchemeRelationRestriction.arrow p.left q.left k

include h in
omit [Mono (a ≫ w)] in
/-- Full restricted endpoints determine their original relation arrow uniquely. -/
theorem selection_hom_ext {Y : Scheme.{u}}
    (x y : Y ⟶ SchemeRelationRestriction.doubleDomain p.left q.left k)
    (hx : x ≫ p' = y ≫ p') (hy : x ≫ q' = y ≫ q') : x = y := by
  have hr : x ≫ r = y ≫ r := by
    apply (cancel_mono (pullback.lift p.left q.left h)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst,
        SchemeRelationRestriction.arrow_fst] using congrArg (fun z ↦ z ≫ k) hx
    · simpa only [Category.assoc, pullback.lift_snd,
        SchemeRelationRestriction.arrow_snd] using congrArg (fun z ↦ z ≫ k) hy
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [SchemeRelationRestriction.arrow, Category.assoc] using hr
    · simpa only [SchemeRelationRestriction.fst, Category.assoc] using hx
  · exact hy

variable {Y : Scheme.{u}} (x y : Y ⟶ C) (hxy : x ≫ k ≫ w = y ≫ k ≫ w)

/-- Lift every coefficient-equal pair to the actual original arrow scheme. -/
def selectionArrow : Y ⟶ D.left :=
  lift e w h a (x ≫ t) (y ≫ t) (by simpa only [← hk, Category.assoc] using hxy)

omit [Mono (pullback.lift p.left q.left h)] in
@[reassoc]
theorem selectionArrow_fst : selectionArrow e w h a k t hk x y hxy ≫ p.left = x ≫ k := by
  rw [selectionArrow, lift_fst, Category.assoc, hk]

omit [Mono (pullback.lift p.left q.left h)] in
@[reassoc]
theorem selectionArrow_snd : selectionArrow e w h a k t hk x y hxy ≫ q.left = y ≫ k := by
  rw [selectionArrow, lift_snd, Category.assoc, hk]

include e h hk in
/-- The FULL original relation on every selection is the actual coefficient kernel. -/
theorem selection_isPullback : IsPullback p' q' (k ≫ w) (k ≫ w) := by
  have H : p' ≫ (k ≫ w) = q' ≫ (k ≫ w) := by
    rw [← Category.assoc, ← Category.assoc,
      ← SchemeRelationRestriction.arrow_fst, ← SchemeRelationRestriction.arrow_snd]
    rw [Category.assoc, Category.assoc, h]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk H
    (fun c ↦ SchemeRelationRestriction.lift p.left q.left k
      (selectionArrow e w h a k t hk c.fst c.snd c.condition) c.fst c.snd
      (selectionArrow_fst e w h a k t hk c.fst c.snd c.condition)
      (selectionArrow_snd e w h a k t hk c.fst c.snd c.condition))
    (fun _ ↦ SchemeRelationRestriction.lift_fst ..)
    (fun _ ↦ SchemeRelationRestriction.lift_snd ..) ?_)
  intro c z hz₁ hz₂
  apply selection_hom_ext w h k
  · exact hz₁.trans (SchemeRelationRestriction.lift_fst ..).symm
  · exact hz₂.trans (SchemeRelationRestriction.lift_snd ..).symm

end FLT.Mazur.SchemeRelationMonicSeedKernel
