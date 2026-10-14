/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOrbitAtlasKernel
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

include e h ha in
/-- The existing full orbit kernel retains the original coefficient morphism. -/
theorem branch_isPullback : IsPullback (fst p.left q.left b) (snd p.left q.left b)
    (b ≫ w) (b ≫ w) := by
  rw [SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a]
  exact SchemeRelationOrbitAtlas.model_isPullback e a (a ≫ w) ha

/-- The propagated coefficient kernel has an actual original arrow on the entire scheme. -/
def branchKernelLift : pullback (b ≫ w) (b ≫ w) ⟶ D.left :=
  (branch_isPullback e w h a ha).lift (pullback.fst _ _) (pullback.snd _ _)
    pullback.condition ≫ arrow p.left q.left b

@[reassoc]
theorem branchKernelLift_fst : branchKernelLift e w h a ha ≫ p.left =
    pullback.fst (b ≫ w) (b ≫ w) ≫ b := by
  rw [branchKernelLift, Category.assoc, arrow_fst, IsPullback.lift_fst_assoc]

@[reassoc]
theorem branchKernelLift_snd : branchKernelLift e w h a ha ≫ q.left =
    pullback.snd (b ≫ w) (b ≫ w) ≫ b := by
  rw [branchKernelLift, Category.assoc, arrow_snd, IsPullback.lift_snd_assoc]

/-- The lift preserves the canonical map of full scheme kernels. -/
theorem branchKernelLift_comp : branchKernelLift e w h a ha ≫ pullback.lift p.left q.left h =
    pullback.map (b ≫ w) (b ≫ w) w w b b (𝟙 T)
      (Category.comp_id _) (Category.comp_id _) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, branchKernelLift_fst, pullback.map]
  · simp only [Category.assoc, pullback.lift_snd, branchKernelLift_snd, pullback.map]

include e ha in
/-- All residue-field branches above two propagated endpoints lie in the original kernel image. -/
theorem mem_image_of_endpoints (x : (pullback w w : Scheme))
    (hx : pullback.fst w w x ∈ Set.range b)
    (hy : pullback.snd w w x ∈ Set.range b) :
    x ∈ Set.range (pullback.lift p.left q.left h) := by
  have hr : x ∈ Set.range (pullback.map (b ≫ w) (b ≫ w) w w b b (𝟙 T)
      (Category.comp_id _) (Category.comp_id _)) := by
    rw [Scheme.Pullback.range_map]
    exact ⟨hx, hy⟩
  obtain ⟨z, hz⟩ := hr
  exact ⟨branchKernelLift e w h a ha z,
    (congrArg (fun t ↦ t z) (branchKernelLift_comp e w h a ha)).trans hz⟩

include e ha in
/-- Source orbit coverage yields the whole coefficient kernel fiber, without a monic seed. -/
theorem fiber_subset_image (t : T)
    (hc : ∀ x : A.left, w x = t → x ∈ Set.range b) :
    ∀ x : (pullback w w : Scheme), (pullback.fst w w ≫ w) x = t →
      x ∈ Set.range (pullback.lift p.left q.left h) := by
  intro x hx
  apply mem_image_of_endpoints e w h a ha x (hc _ hx)
  apply hc
  have he := congrArg (fun g ↦ g x) (pullback.condition (f := w) (g := w))
  exact he.symm.trans hx

end FLT.Mazur.SchemeRelationNonsplitSeed
