/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring
public import FLT.Mazur.SchemeRelationEtaleBranchPropagation

/-!
# Propagating full kernels from nonsplit seeds

A full kernel on a seed propagates along original arrows. The two seed
coordinates remain independent: their original relation arrow, rather than
an equality of the coordinates, transports the kernel test back to the source.
No monicity of the seed over the coefficient target is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationNonsplitSeed
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  (ha : IsPullback (fst p.left q.left a) (snd p.left q.left a) (a ≫ w) (a ≫ w))
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "r" => pullback.fst q.left a
local notation "s" => pullback.snd q.left a
variable {Y : Scheme.{u}} (x y : Y ⟶ pullback q.left a)
  (hxy : x ≫ (SchemeRelationEtaleBranchPropagation.branch p.left q.left a ≫ w) =
    y ≫ (SchemeRelationEtaleBranchPropagation.branch p.left q.left a ≫ w))

include h hxy in
/-- Coefficient equality retains two independent seed coordinates. -/
theorem seed_condition : (x ≫ s) ≫ (a ≫ w) = (y ≫ s) ≫ (a ≫ w) := by
  simpa only [Category.assoc,
    ← SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a] using hxy

/-- The seed kernel constructs an actual original arrow between the seed coordinates. -/
def seedArrow : Y ⟶ D.left :=
  ha.lift (x ≫ s) (y ≫ s) (seed_condition w h a x y hxy) ≫ arrow p.left q.left a

@[reassoc]
theorem seedArrow_fst : seedArrow w h a ha x y hxy ≫ p.left = (x ≫ r) ≫ q.left := by
  rw [seedArrow, Category.assoc, arrow_fst, ← Category.assoc, ha.lift_fst]
  simp only [Category.assoc, pullback.condition]

@[reassoc]
theorem seedArrow_snd : seedArrow w h a ha x y hxy ≫ q.left = (y ≫ r) ≫ q.left := by
  rw [seedArrow, Category.assoc, arrow_snd, ← Category.assoc, ha.lift_snd]
  simp only [Category.assoc, pullback.condition]

/-- Transport the seed arrow back along the original arrows, without identifying seeds. -/
def kernelArrow : Y ⟶ D.left :=
  untransportOriginal e (x ≫ r) (y ≫ r) (seedArrow w h a ha x y hxy)
    (seedArrow_fst w h a ha x y hxy) (seedArrow_snd w h a ha x y hxy)

@[reassoc]
theorem kernelArrow_fst : kernelArrow e w h a ha x y hxy ≫ p.left = x ≫ b := by
  rw [kernelArrow, untransportOriginal_fst]
  rfl

@[reassoc]
theorem kernelArrow_snd : kernelArrow e w h a ha x y hxy ≫ q.left = y ≫ b := by
  rw [kernelArrow, untransportOriginal_snd]
  rfl

/-- The full two-coordinate restricted relation receives every coefficient kernel test. -/
def kernelLift : Y ⟶ doubleDomain p.left q.left b :=
  lift p.left q.left b (kernelArrow e w h a ha x y hxy) x y
    (kernelArrow_fst e w h a ha x y hxy) (kernelArrow_snd e w h a ha x y hxy)

@[reassoc]
theorem kernelLift_fst : kernelLift e w h a ha x y hxy ≫ fst p.left q.left b = x :=
  lift_fst ..

@[reassoc]
theorem kernelLift_snd : kernelLift e w h a ha x y hxy ≫ snd p.left q.left b = y :=
  lift_snd ..

include h in
/-- The original coefficient equation holds on the entire propagated relation. -/
theorem branch_condition : fst p.left q.left b ≫ (b ≫ w) =
    snd p.left q.left b ≫ (b ≫ w) := by
  rw [← Category.assoc, ← Category.assoc, ← arrow_fst, ← arrow_snd]
  rw [Category.assoc, Category.assoc, h]

include e h ha in
/-- A full nonsplit seed kernel constructs the full kernel on the propagated source. -/
theorem branch_isPullback : IsPullback (fst p.left q.left b) (snd p.left q.left b)
    (b ≫ w) (b ≫ w) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (branch_condition w h a)
    (fun c ↦ kernelLift e w h a ha c.fst c.snd c.condition)
    (fun c ↦ kernelLift_fst e w h a ha c.fst c.snd c.condition)
    (fun c ↦ kernelLift_snd e w h a ha c.fst c.snd c.condition) ?_)
  intro c z hz₁ hz₂
  apply SchemeRelationReanchoring.endpoint_ext e b
  · exact hz₁.trans (kernelLift_fst e w h a ha c.fst c.snd c.condition).symm
  · exact hz₂.trans (kernelLift_snd e w h a ha c.fst c.snd c.condition).symm

end FLT.Mazur.SchemeRelationNonsplitSeed
