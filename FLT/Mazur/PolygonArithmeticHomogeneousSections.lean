/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompatibleAlgebra

/-!
# Compatible homogeneous polygon sections

A degree consists of compatible actual stage sections which are homogeneous
of that same degree at every stage. Finite sums of these degrees form a
commutative algebra over the integral coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Compatibility with a fixed homogeneous degree at every stage. -/
def IsCompatibleDegree (k : ℕ) (s : CompatibleSections A π n h) : Prop :=
  ∀ m, compatibleEval A π n h m s ∈ grade (boundaryLine A π m n h) ⊤ k

/-- Zero is a compatible homogeneous section in every degree. -/
theorem isCompatibleDegree_zero (k : ℕ) : IsCompatibleDegree A π n h k 0 := by
  intro m
  rw [map_zero]
  exact (grade (boundaryLine A π m n h) ⊤ k).zero_mem

/-- Addition preserves a fixed compatible degree. -/
theorem isCompatibleDegree_add (k : ℕ) {s t : CompatibleSections A π n h}
    (hs : IsCompatibleDegree A π n h k s) (ht : IsCompatibleDegree A π n h k t) :
    IsCompatibleDegree A π n h k (s + t) := by
  intro m
  rw [map_add]
  exact (grade (boundaryLine A π m n h) ⊤ k).add_mem (hs m) (ht m)

/-- Original-base scalars preserve every compatible tensor degree. -/
theorem isCompatibleDegree_smul (k : ℕ) (r : A)
    {s : CompatibleSections A π n h} (hs : IsCompatibleDegree A π n h k s) :
    IsCompatibleDegree A π n h k (r • s) := by
  intro m
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap,
    boundaryIntegralScalars_eq, ← zero_add k]
  exact mul_mem_grade (boundaryLine A π m n h) ⊤ ⟨_, rfl⟩ (hs m)

/-- A fixed tensor degree across all actual arithmetic stages. -/
def compatibleSectionDegree (k : ℕ) :
    Submodule A (CompatibleSections A π n h) where
  carrier := IsCompatibleDegree A π n h k
  zero_mem' := isCompatibleDegree_zero A π n h k
  add_mem' := isCompatibleDegree_add A π n h k
  smul_mem' r _s hs := isCompatibleDegree_smul A π n h k r hs

/-- The compatible unit has degree zero. -/
theorem compatibleSectionDegree_one :
    (1 : CompatibleSections A π n h) ∈ compatibleSectionDegree A π n h 0 := by
  intro m
  rw [map_one]
  exact one_mem_grade (boundaryLine A π m n h) ⊤

/-- Multiplication adds the degrees of compatible homogeneous sections. -/
theorem compatibleSectionDegree_mul {i j : ℕ} {s t : CompatibleSections A π n h}
    (hs : s ∈ compatibleSectionDegree A π n h i) (ht : t ∈ compatibleSectionDegree A π n h j) :
    s * t ∈ compatibleSectionDegree A π n h (i + j) := by
  intro m
  rw [map_mul]
  exact mul_mem_grade (boundaryLine A π m n h) ⊤ (hs m) (ht m)

/-- The compatible homogeneous degrees contain the unit and multiply by adding degrees. -/
instance compatibleSectionDegree_graded :
    SetLike.GradedMonoid (compatibleSectionDegree A π n h) where
  one_mem := compatibleSectionDegree_one A π n h
  mul_mem := fun _ _ _ _ hs ht ↦ compatibleSectionDegree_mul A π n h hs ht

/-- The algebra formed degreewise from compatible sections, with finite degree support. -/
abbrev CompatibleGradedSections := ⨁ k : ℕ, compatibleSectionDegree A π n h k

/-- Compatible sections multiply to give a commutative graded ring. -/
instance compatibleGradedSectionsCommRing : CommRing (CompatibleGradedSections A π n h) :=
  inferInstanceAs (CommRing (⨁ k : ℕ, compatibleSectionDegree A π n h k))

/-- The actual integral coefficient base acts in degree zero. -/
instance compatibleGradedSectionsAlgebra :
    Algebra A (CompatibleGradedSections A π n h) := inferInstance

/-- Finite sums of compatible homogeneous sections give compatible full sections. -/
def compatibleGradedToSections :
    CompatibleGradedSections A π n h →+* CompatibleSections A π n h :=
  DirectSum.coeRingHom (compatibleSectionDegree A π n h)

/-- The degreewise algebra projects to the original full section ring at each stage. -/
def compatibleGradedEval (m : ℕ) :
    CompatibleGradedSections A π n h →+* boundaryGradedSections A π n h m :=
  (compatibleEval A π n h m).comp (compatibleGradedToSections A π n h)

/-- Every homogeneous insertion evaluates to its specified actual stage section. -/
theorem compatibleGradedEval_of (m k : ℕ) (s : compatibleSectionDegree A π n h k) :
    compatibleGradedEval A π n h m (DirectSum.of _ k s) = compatibleEval A π n h m s := by
  change compatibleEval A π n h m
    (DirectSum.coeRingHom (compatibleSectionDegree A π n h) (DirectSum.of _ k s)) = _
  rw [DirectSum.coeRingHom_of]

/-- Degreewise construction retains every specified stage transition. -/
theorem compatibleGradedEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap A π n h f).comp (compatibleGradedEval A π n h b) =
      compatibleGradedEval A π n h a := by
  rw [compatibleGradedEval, ← RingHom.comp_assoc, compatibleEval_transition]
  rfl

end FLT.Mazur.PolygonArithmeticStages
