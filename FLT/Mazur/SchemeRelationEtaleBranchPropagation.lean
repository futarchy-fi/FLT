/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEtaleSourceBranch

/-!
# Propagating a source branch along the complete original relation

Pull back the second endpoint to the branch and project by the first endpoint.
This constructs an etale branch over both source and target whenever the seed
has those properties. Point coverage of a full kernel fiber then makes this
new branch cover the entire source fiber, without assuming inverse morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationEtaleBranchPropagation
set_option backward.isDefEq.respectTransparency false
variable {D A T Z : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)
  (h : p ≫ w = q ≫ w) (a : Z ⟶ A)

/-- The branch consists of actual original arrows with their second endpoint on the seed. -/
def branch : pullback q a ⟶ A := pullback.fst q a ≫ p

include h in
/-- Its coefficient map is the original seed coefficient map after the etale endpoint pullback. -/
@[reassoc]
theorem branch_comp : branch p q a ≫ w = pullback.snd q a ≫ (a ≫ w) := by
  rw [branch, Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc]

instance branch_etale [Etale p] [Etale a] : Etale (branch p q a) :=
  inferInstanceAs (Etale (pullback.fst q a ≫ p))

include h in
/-- Etaleness over the coefficient target propagates through original arrows. -/
theorem branch_target_etale [Etale q] [Etale (a ≫ w)] : Etale (branch p q a ≫ w) := by
  rw [branch_comp p q w h a]
  infer_instance

local notation "m" => pullback.lift p q h
local notation "v" => pullback.fst w w ≫ w

/-- One seed point and full kernel point coverage give coverage of the entire source fiber. -/
theorem fiber_subset_branch (z : Z)
    (hg : ∀ x : (pullback w w : Scheme), v x = (a ≫ w) z → x ∈ Set.range m) :
    ∀ x : A, w x = (a ≫ w) z → x ∈ Set.range (branch p q a) := by
  intro x hx
  obtain ⟨k, hk₁, hk₂⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback w w) x (a z) hx
  have hk : v k = (a ≫ w) z := by
    change w (pullback.fst w w k) = _
    rw [hk₁, hx]
  obtain ⟨r, hr⟩ := hg k hk
  have hp : p r = x := by
    rw [← pullback.lift_fst p q h, Scheme.Hom.comp_apply, hr, hk₁]
  have hq : q r = a z := by
    rw [← pullback.lift_snd p q h, Scheme.Hom.comp_apply, hr, hk₂]
  obtain ⟨s, hs, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback q a) r z hq
  exact ⟨s, (congrArg p hs).trans hp⟩

/-- A nonempty etale seed over an irreducible target meets its actual generic point. -/
theorem exists_generic_seed [IrreducibleSpace T] [Etale (a ≫ w)] [Nonempty Z] :
    ∃ z : Z, (a ≫ w) z = genericPoint T := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hg : genericPoint T ∈ Set.range (a ≫ w) :=
    (genericPoint_specializes ((a ≫ w) z)).mem_open
      (a ≫ w).isOpenMap.isOpen_range ⟨z, rfl⟩
  exact hg

end FLT.Mazur.SchemeRelationEtaleBranchPropagation
