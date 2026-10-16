/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFrameRebaseLaws

/-!
# The scheme of endpoint-normalized relation frames

The distinguished coordinate has second endpoint equal to the first endpoint.
This is imposed by an actual equalizer of scheme morphisms. All other second
endpoints remain independent. The defining equation determines the first endpoint,
so all second endpoints together determine maps into this scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p q : D ⟶ A) [IsSeparated p]
  (I : Type) [Fintype I] (o : I)

local instance normalizedOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "F" => distinctScheme (Over.mk p) I

/-- An actual scheme imposing the distinguished-endpoint equation. -/
def source : Scheme := equalizer (F).hom ((distinctCoordinate (Over.mk p) I o).left ≫ q)

/-- The inclusion retains the original full distinct frame. -/
def inclusion : source p q I o ⟶ (F).left := equalizer.ι _ _

instance inclusion_mono : Mono (inclusion p q I o) := inferInstanceAs (Mono (equalizer.ι _ _))

/-- The original first endpoint of a normalized frame. -/
def first : source p q I o ⟶ A := inclusion p q I o ≫ (F).hom

/-- Each original relation coordinate on the normalized source. -/
def coordinate (i : I) : source p q I o ⟶ D :=
  inclusion p q I o ≫ (distinctCoordinate (Over.mk p) I i).left

/-- Every coordinate has the original first endpoint. -/
@[reassoc] theorem coordinate_first (i : I) :
    coordinate p q I o i ≫ p = first p q I o := by
  rw [coordinate, Category.assoc]
  exact congrArg (fun z ↦ inclusion p q I o ≫ z)
    (distinctCoordinate (Over.mk p) I i).w

/-- Normalization is an equality of scheme morphisms, not only of geometric points. -/
theorem first_eq_distinguished : first p q I o = coordinate p q I o o ≫ q := by
  exact (equalizer.condition _ _).trans (Category.assoc _ _ _).symm

/-- The universal normalized frame over its original first endpoint. -/
def frame : Over.mk (first p q I o) ⟶ F := Over.homMk (inclusion p q I o) rfl

variable {T : Scheme}

/-- Any frame satisfying the exact endpoint equation lifts to the normalized scheme. -/
def lift {b : T ⟶ A} (t : Over.mk b ⟶ F)
    (h : b = (t ≫ distinctCoordinate (Over.mk p) I o).left ≫ q) : T ⟶ source p q I o :=
  equalizer.lift t.left (by
    rw [t.w]
    exact h.trans (Category.assoc _ _ _))

/-- The equalizer lift keeps the entire original frame. -/
@[reassoc] theorem lift_inclusion {b : T ⟶ A} (t : Over.mk b ⟶ F) (h) :
    lift p q I o t h ≫ inclusion p q I o = t.left := equalizer.lift_ι _ _

/-- The lift keeps every original relation coordinate. -/
@[reassoc] theorem lift_coordinate {b : T ⟶ A} (t : Over.mk b ⟶ F) (h) (i : I) :
    lift p q I o t h ≫ coordinate p q I o i =
      (t ≫ distinctCoordinate (Over.mk p) I i).left := by
  rw [coordinate, ← Category.assoc, lift_inclusion]
  rfl

/-- The lift retains its displayed first endpoint. -/
@[reassoc] theorem lift_first {b : T ⟶ A} (t : Over.mk b ⟶ F) (h) :
    lift p q I o t h ≫ first p q I o = b := by
  rw [first, ← Category.assoc, lift_inclusion]
  exact t.w

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Maps into normalized frames are determined by all original second endpoints. -/
theorem hom_ext_second {u v : T ⟶ source p q I o}
    (h : ∀ i, u ≫ coordinate p q I o i ≫ q = v ≫ coordinate p q I o i ≫ q) : u = v := by
  have hb : u ≫ first p q I o = v ≫ first p q I o := by
    rw [first_eq_distinguished]
    exact h o
  let a : Over.mk (u ≫ first p q I o) ⟶ F :=
    Over.homMk (u ≫ inclusion p q I o) (Category.assoc _ _ _)
  let b : Over.mk (u ≫ first p q I o) ⟶ F :=
    Over.homMk (v ≫ inclusion p q I o) ((Category.assoc _ _ _).trans hb.symm)
  have hab : a = b := by
    apply frame_ext_second e I
    intro i
    change ((u ≫ inclusion p q I o) ≫ (distinctCoordinate (Over.mk p) I i).left) ≫ q =
      ((v ≫ inclusion p q I o) ≫ (distinctCoordinate (Over.mk p) I i).left) ≫ q
    simpa only [coordinate, Category.assoc] using h i
  exact (cancel_mono (inclusion p q I o)).mp (congrArg Over.Hom.left hab)

/-- The distinguished relation coordinate is exactly the identity original arrow. -/
theorem distinguished_eq_identity : coordinate p q I o o = first p q I o ≫ e.r := by
  apply e.right_cancellation
  · rw [coordinate_first, Category.assoc, e.reflexivity₁, Category.comp_id]
  · rw [← first_eq_distinguished, Category.assoc, e.reflexivity₂, Category.comp_id]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
