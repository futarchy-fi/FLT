/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleSectionAlgebra

/-!
# Compatible homogeneous polygon sections

A degree consists of compatible actual stage sections which are homogeneous
of that same degree at every stage. Finite sums of these degrees form a
commutative algebra over the complete coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- Compatibility with a fixed homogeneous degree at every stage. -/
def IsCompatibleDegree (k : ℕ) (s : CompatibleSections R n h) : Prop :=
  ∀ m, compatibleEval R n h m s ∈ grade (boundaryLine R m n h) ⊤ k

/-- Zero is a compatible homogeneous section in every degree. -/
theorem isCompatibleDegree_zero (k : ℕ) : IsCompatibleDegree R n h k 0 := by
  intro m
  rw [map_zero]
  exact (grade (boundaryLine R m n h) ⊤ k).zero_mem

/-- Addition preserves a fixed compatible degree. -/
theorem isCompatibleDegree_add (k : ℕ) {s t : CompatibleSections R n h}
    (hs : IsCompatibleDegree R n h k s) (ht : IsCompatibleDegree R n h k t) :
    IsCompatibleDegree R n h k (s + t) := by
  intro m
  rw [map_add]
  exact (grade (boundaryLine R m n h) ⊤ k).add_mem (hs m) (ht m)

/-- Complete-base scalars preserve every compatible tensor degree. -/
theorem isCompatibleDegree_smul (k : ℕ) (r : PowerSeries R)
    {s : CompatibleSections R n h} (hs : IsCompatibleDegree R n h k s) :
    IsCompatibleDegree R n h k (r • s) := by
  intro m
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap,
    boundarySeriesScalars_eq, ← zero_add k]
  exact mul_mem_grade (boundaryLine R m n h) ⊤ ⟨_, rfl⟩ (hs m)

/-- A fixed tensor degree across all actual infinitesimal stages. -/
def compatibleSectionDegree (k : ℕ) :
    Submodule (PowerSeries R) (CompatibleSections R n h) where
  carrier := IsCompatibleDegree R n h k
  zero_mem' := isCompatibleDegree_zero R n h k
  add_mem' := isCompatibleDegree_add R n h k
  smul_mem' r _s hs := isCompatibleDegree_smul R n h k r hs

/-- The compatible unit has degree zero. -/
theorem compatibleSectionDegree_one :
    (1 : CompatibleSections R n h) ∈ compatibleSectionDegree R n h 0 := by
  intro m
  rw [map_one]
  exact one_mem_grade (boundaryLine R m n h) ⊤

/-- Multiplication adds the degrees of compatible homogeneous sections. -/
theorem compatibleSectionDegree_mul {i j : ℕ} {s t : CompatibleSections R n h}
    (hs : s ∈ compatibleSectionDegree R n h i) (ht : t ∈ compatibleSectionDegree R n h j) :
    s * t ∈ compatibleSectionDegree R n h (i + j) := by
  intro m
  rw [map_mul]
  exact mul_mem_grade (boundaryLine R m n h) ⊤ (hs m) (ht m)

/-- The compatible homogeneous degrees contain the unit and multiply by adding degrees. -/
instance compatibleSectionDegree_graded : SetLike.GradedMonoid (compatibleSectionDegree R n h) where
  one_mem := compatibleSectionDegree_one R n h
  mul_mem := fun _ _ _ _ hs ht ↦ compatibleSectionDegree_mul R n h hs ht

/-- The algebra formed degreewise from compatible sections, with finite degree support. -/
abbrev CompatibleGradedSections := ⨁ k : ℕ, compatibleSectionDegree R n h k

/-- Compatible sections multiply to give a commutative graded ring. -/
instance compatibleGradedSectionsCommRing : CommRing (CompatibleGradedSections R n h) :=
  inferInstanceAs (CommRing (⨁ k : ℕ, compatibleSectionDegree R n h k))

/-- The actual complete coefficient base acts in degree zero. -/
instance compatibleGradedSectionsAlgebra :
    Algebra (PowerSeries R) (CompatibleGradedSections R n h) := inferInstance

/-- Finite sums of compatible homogeneous sections give compatible full sections. -/
def compatibleGradedToSections :
    CompatibleGradedSections R n h →+* CompatibleSections R n h :=
  DirectSum.coeRingHom (compatibleSectionDegree R n h)

/-- The degreewise algebra projects to the original full section ring at each stage. -/
def compatibleGradedEval (m : ℕ) :
    CompatibleGradedSections R n h →+* boundaryGradedSections R n h m :=
  (compatibleEval R n h m).comp (compatibleGradedToSections R n h)

/-- Every homogeneous insertion evaluates to its specified actual stage section. -/
theorem compatibleGradedEval_of (m k : ℕ) (s : compatibleSectionDegree R n h k) :
    compatibleGradedEval R n h m (DirectSum.of _ k s) = compatibleEval R n h m s := by
  change compatibleEval R n h m
    (DirectSum.coeRingHom (compatibleSectionDegree R n h) (DirectSum.of _ k s)) = _
  rw [DirectSum.coeRingHom_of]

/-- Degreewise construction retains every specified stage transition. -/
theorem compatibleGradedEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap R n h f).comp (compatibleGradedEval R n h b) =
      compatibleGradedEval R n h a := by
  rw [compatibleGradedEval, ← RingHom.comp_assoc, compatibleEval_transition]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
