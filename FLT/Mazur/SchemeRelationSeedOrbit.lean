/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedImage

/-!
# Detecting propagated seed images by original point orbits

A source belongs to the propagated seed image exactly when its original
relation orbit meets the seed. With a monic etale target seed, this condition
on a source fiber is equivalent to coverage of its full coefficient kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "m" => pullback.lift p.left q.left h

/-- Propagation uses the actual point relation, without adding an equivalence closure. -/
theorem mem_branch_iff_related (x : A.left) :
    x ∈ Set.range b ↔ ∃ z : Z, RelativeRelationOrbit.Related p q x (a z) := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨pullback.snd q.left a s, pullback.fst q.left a s, rfl, ?_⟩
    exact congrArg (fun t ↦ t s) (pullback.condition (f := q.left) (g := a))
  · rintro ⟨z, r, hr, hz⟩
    obtain ⟨s, hs, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback q.left a) r z hz
    exact ⟨s, (congrArg p.left hs).trans hr⟩

include e

/-- A seed over the specified target point reduces full kernel coverage to original orbits. -/
theorem fiber_image_iff_orbits [Mono (a ≫ w)] (z : Z) :
    (∀ x : (pullback w w : Scheme), (pullback.fst w w ≫ w) x = (a ≫ w) z →
      x ∈ Set.range m) ↔
    ∀ x : A.left, w x = (a ≫ w) z →
      ∃ y : Z, RelativeRelationOrbit.Related p q x (a y) := by
  constructor
  · intro hg x hx
    exact (mem_branch_iff_related a x).mp
      (SchemeRelationEtaleBranchPropagation.fiber_subset_branch p.left q.left w h a z hg x hx)
  · intro hc
    exact fiber_subset_image e w h a ((a ≫ w) z)
      (fun x hx ↦ (mem_branch_iff_related a x).mpr (hc x hx))

/-- One nonempty etale target seed suffices to test the entire generic kernel by source orbits. -/
theorem generic_image_iff_orbits [Mono (a ≫ w)] [Etale (a ≫ w)]
    [IrreducibleSpace T] [Nonempty Z] :
    (∀ x : (pullback w w : Scheme), (pullback.fst w w ≫ w) x = genericPoint T →
      x ∈ Set.range m) ↔
    ∀ x : A.left, w x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z) := by
  obtain ⟨z, hz⟩ := SchemeRelationEtaleBranchPropagation.exists_generic_seed w a
  simpa only [hz] using fiber_image_iff_orbits e w h a z

end FLT.Mazur.SchemeRelationMonicSeedKernel
