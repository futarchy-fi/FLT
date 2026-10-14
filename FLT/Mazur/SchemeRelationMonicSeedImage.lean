/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedKernel

/-!
# Kernel point coverage from source orbit coverage

The kernel of the propagated source branch maps onto precisely the strip
whose two endpoints meet that branch. Its scheme lift to the original
relation therefore covers every point of this strip, including independent
residue-field branches of the fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left) [Mono (a ≫ w)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "m" => pullback.lift p.left q.left h

/-- The kernel of the propagated branch has an actual map to the full original relation. -/
def branchKernelLift : pullback (b ≫ w) (b ≫ w) ⟶ D.left :=
  lift e w h a (pullback.fst (b ≫ w) (b ≫ w))
    (pullback.snd (b ≫ w) (b ≫ w)) pullback.condition

/-- Its comparison is precisely the canonical morphism between the two scheme kernels. -/
theorem branchKernelLift_comp : branchKernelLift e w h a ≫ m =
    pullback.map (b ≫ w) (b ≫ w) w w b b (𝟙 T)
      (Category.comp_id _) (Category.comp_id _) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      branchKernelLift, lift_fst]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      branchKernelLift, lift_snd]

include e

/-- Coverage of both source endpoints covers ALL points of the candidate kernel strip. -/
theorem mem_image_of_endpoints (x : (pullback w w : Scheme))
    (hx : pullback.fst w w x ∈ Set.range b)
    (hy : pullback.snd w w x ∈ Set.range b) : x ∈ Set.range m := by
  have hr : x ∈ Set.range (pullback.map (b ≫ w) (b ≫ w) w w b b (𝟙 T)
      (Category.comp_id _) (Category.comp_id _)) := by
    rw [Scheme.Pullback.range_map]
    exact ⟨hx, hy⟩
  obtain ⟨z, hz⟩ := hr
  refine ⟨branchKernelLift e w h a z, ?_⟩
  exact (congrArg (fun t ↦ t z) (branchKernelLift_comp e w h a)).trans hz

/-- A whole source fiber covered by the propagated branch gives whole kernel fiber coverage. -/
theorem fiber_subset_image (t : T)
    (hc : ∀ x : A.left, w x = t → x ∈ Set.range b) :
    ∀ x : (pullback w w : Scheme), (pullback.fst w w ≫ w) x = t →
      x ∈ Set.range m := by
  intro x hx
  apply mem_image_of_endpoints e w h a x (hc _ hx)
  apply hc
  have he := congrArg (fun g ↦ g x) (pullback.condition (f := w) (g := w))
  exact he.symm.trans hx

end FLT.Mazur.SchemeRelationMonicSeedKernel
