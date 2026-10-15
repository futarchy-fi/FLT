/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedMarkings
public import FLT.Mazur.PolygonArithmeticResidueNilpotence

/-!
# A common affine neighborhood for all orders of an original marking

Each truncated coefficient spectrum has one point. Naturality therefore
puts every order of a compatible point in any neighborhood of its closed point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hgen in
/-- Nilpotent thickening of a field spectrum still has only one point. -/
theorem stageBase_subsingleton (m : ℕ) : Subsingleton (Spec (.of (Quotient A π m))) :=
  (residueBase_surjective A π hgen (parameter_residue_zero A π hgen) m).surj.subsingleton

/-- The unique point of the actual truncated coefficient spectrum. -/
def stageBasePoint (m : ℕ) : Spec (.of (Quotient A π m)) :=
  residueBase A π (parameter_residue_zero A π hgen) m
    (default : Spec (.of (IsLocalRing.ResidueField A)))

variable {X : Scheme} (s : baseSystem A π ⟶ (Functor.const ℕ).obj X)

/-- Every order of a compatible point has the same underlying image. -/
theorem compatiblePoint_apply (m : ℕ) (x : Spec (.of (Quotient A π m))) :
    s.app m x = s.app 0 (stageBasePoint A π hgen 0) := by
  have hn := s.naturality (homOfLE (Nat.zero_le m))
  simp only [Functor.const_obj_map] at hn
  have he := congrArg (fun f : Spec (.of (Quotient A π 0)) ⟶ X ↦ f (stageBasePoint A π hgen 0)) hn
  change s.app m ((baseSystem A π).map _ (stageBasePoint A π hgen 0)) = _ at he
  exact (congrArg (s.app m) ((stageBase_subsingleton A π hgen m).elim _ _)).trans he

include hgen in
/-- One affine open contains all the original finite-order maps of a compatible point. -/
theorem compatiblePoint_exists_affine :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ m, Set.range (s.app m) ⊆ (U : Set X) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := s.app 0 (stageBasePoint A π hgen 0)) trivial
  refine ⟨U, hU, fun m y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hy
  rwa [compatiblePoint_apply A π hgen s m x]

variable [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- All actual finite-order polygon markings land in one affine neighborhood. -/
theorem originalMarking_exists_affine (i : Fin n) :
    ∃ U : (exactVeroneseProj A π n h hne hgen).Opens, IsAffineOpen U ∧
      ∀ m, Set.range ((originalMarkingCompatibleProj A π hne hgen n h i).app m) ⊆
        (U : Set (exactVeroneseProj A π n h hne hgen)) :=
  compatiblePoint_exists_affine A π hgen (originalMarkingCompatibleProj A π hne hgen n h i)

end FLT.Mazur.PolygonArithmeticStages
