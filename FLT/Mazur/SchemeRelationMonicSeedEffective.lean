/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedKernel
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# An effective full relation on the propagated seed source

Reselect the source by propagating a monic seed along original arrows. Its
full two-endpoint restriction is the actual coefficient kernel, on all scheme
tests. No generic coverage or irreducibility hypothesis is needed on this
constructed source. Coverage of the unrestricted source remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left) [Mono (a ≫ w)]
  [Mono (pullback.lift p.left q.left h)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "p'" => SchemeRelationRestriction.fst p.left q.left b
local notation "q'" => SchemeRelationRestriction.snd p.left q.left b
local notation "r" => SchemeRelationRestriction.arrow p.left q.left b

include h

omit [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)] in
/-- The FULL restricted relation keeps the original coefficient equation. -/
theorem branch_condition : p' ≫ (b ≫ w) = q' ≫ (b ≫ w) := by
  rw [← Category.assoc, ← Category.assoc,
    ← SchemeRelationRestriction.arrow_fst, ← SchemeRelationRestriction.arrow_snd]
  rw [Category.assoc, Category.assoc, h]

omit [Mono (a ≫ w)] in
/-- Independent source lifts and the original arrow determine the full restriction uniquely. -/
theorem branch_hom_ext {Y : Scheme.{u}}
    (x y : Y ⟶ SchemeRelationRestriction.doubleDomain p.left q.left b)
    (hx : x ≫ p' = y ≫ p') (hy : x ≫ q' = y ≫ q') : x = y := by
  have hr : x ≫ r = y ≫ r := by
    apply (cancel_mono (pullback.lift p.left q.left h)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst,
        SchemeRelationRestriction.arrow_fst] using congrArg (fun t ↦ t ≫ b) hx
    · simpa only [Category.assoc, pullback.lift_snd,
        SchemeRelationRestriction.arrow_snd] using congrArg (fun t ↦ t ≫ b) hy
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [SchemeRelationRestriction.arrow, Category.assoc] using hr
    · simpa only [SchemeRelationRestriction.fst, Category.assoc] using hx
  · exact hy

variable {Y : Scheme.{u}} (x y : Y ⟶ pullback q.left a)

/-- Construct the full restricted relation arrow of any coefficient-equal source pair. -/
def branchLift (hxy : x ≫ (b ≫ w) = y ≫ (b ≫ w)) :
    Y ⟶ SchemeRelationRestriction.doubleDomain p.left q.left b :=
  SchemeRelationRestriction.lift p.left q.left b (lift e w h a x y hxy) x y
    (lift_fst e w h a x y hxy) (lift_snd e w h a x y hxy)

omit [Mono (pullback.lift p.left q.left h)] in
@[reassoc]
theorem branchLift_fst (hxy : x ≫ (b ≫ w) = y ≫ (b ≫ w)) :
    branchLift e w h a x y hxy ≫ p' = x :=
  SchemeRelationRestriction.lift_fst _ _ _ _ _ _ _ _

omit [Mono (pullback.lift p.left q.left h)] in
@[reassoc]
theorem branchLift_snd (hxy : x ≫ (b ≫ w) = y ≫ (b ≫ w)) :
    branchLift e w h a x y hxy ≫ q' = y :=
  SchemeRelationRestriction.lift_snd _ _ _ _ _ _ _ _

include e in
/-- Reselection by the propagated seed constructs an effective FULL original kernel relation. -/
theorem branch_isPullback : IsPullback p' q' (b ≫ w) (b ≫ w) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (branch_condition w h a)
    (fun c ↦ branchLift e w h a c.fst c.snd c.condition)
    (fun c ↦ branchLift_fst e w h a c.fst c.snd c.condition)
    (fun c ↦ branchLift_snd e w h a c.fst c.snd c.condition) ?_)
  intro c z hz₁ hz₂
  apply branch_hom_ext w h a
  · exact hz₁.trans (branchLift_fst e w h a c.fst c.snd c.condition).symm
  · exact hz₂.trans (branchLift_snd e w h a c.fst c.snd c.condition).symm

end FLT.Mazur.SchemeRelationMonicSeedKernel
