/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonRetainedStageMarkings

/-!
# A common affine neighborhood for all orders of an original marking

Each truncated coefficient spectrum has one point. Naturality therefore
puts every order of a compatible point in any neighborhood of its closed point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K]

/-- Nilpotent thickening of a field spectrum still has only one point. -/
instance stageBase_subsingleton (m : ℕ) : Subsingleton (Spec (.of (Ring K m))) :=
  (Surjective.surj (f := reductionBase K m)).subsingleton

/-- The unique point of the actual truncated coefficient spectrum. -/
def stageBasePoint (m : ℕ) : Spec (.of (Ring K m)) :=
  reductionBase K m (default : Spec (.of K))

variable {X : Scheme} (s : baseSystem K ⟶ (Functor.const ℕ).obj X)

/-- Every order of a compatible point has the same underlying image. -/
theorem compatiblePoint_apply (m : ℕ) (x : Spec (.of (Ring K m))) :
    s.app m x = s.app 0 (stageBasePoint K 0) := by
  have hn := s.naturality (homOfLE (Nat.zero_le m))
  simp only [Functor.const_obj_map] at hn
  have he := congrArg (fun f : Spec (.of (Ring K 0)) ⟶ X ↦ f (stageBasePoint K 0)) hn
  change s.app m ((baseSystem K).map _ (stageBasePoint K 0)) = _ at he
  exact (congrArg (s.app m) ((stageBase_subsingleton K m).elim _ _)).trans he

/-- One affine open contains all the original finite-order maps of a compatible point. -/
theorem compatiblePoint_exists_affine :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ m, Set.range (s.app m) ⊆ (U : Set X) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := s.app 0 (stageBasePoint K 0)) trivial
  refine ⟨U, hU, fun m y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  rwa [compatiblePoint_apply K s m x]

variable (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- All actual finite-order polygon markings land in one affine neighborhood. -/
theorem originalMarking_exists_affine (i : Fin n) :
    ∃ U : (exactVeroneseProj K n h).Opens, IsAffineOpen U ∧
      ∀ m, Set.range ((originalMarkingCompatibleProj K n h i).app m) ⊆
        (U : Set (exactVeroneseProj K n h)) :=
  compatiblePoint_exists_affine K (originalMarkingCompatibleProj K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
