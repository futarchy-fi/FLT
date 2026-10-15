/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSectionAnnihilator
public import FLT.Mazur.PolygonArithmeticDegreeLifting
public import FLT.Mazur.SectionGradedLineKernel

/-!
# Parameter multiplication in the actual graded section rings

The integral-base parameter acts by the original structural parameter on
every homogeneous section. Its annihilator on each degree is the kernel of
the specified adjacent graded-ring map, with no degree bound.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The integral-base parameter is the actual stage structural parameter in degree zero. -/
theorem boundaryIntegralScalars_parameter (m : ℕ) :
    boundaryIntegralScalars A π n h m π =
      algebraMap Γ((family A π m n h).left, ⊤) (boundaryGradedSections A π n h m)
        (stageParameterSection A π m n h) := by
  rw [boundaryIntegralScalars_stage]
  rfl

/-- Multiplication in the stage ring is the original scalar action in every degree. -/
theorem boundaryIntegralScalars_power_of (m k d : ℕ)
    (s : Piece (boundaryLine A π m n h) ⊤ d) :
    boundaryIntegralScalars A π n h m π ^ k * of (boundaryLine A π m n h) ⊤ d s =
      of (boundaryLine A π m n h) ⊤ d (stageParameterSection A π m n h ^ k • s) := by
  rw [boundaryIntegralScalars_parameter, ← map_pow, ← Algebra.smul_def, ← map_smul]

/-- The adjacent ring map is the original specified line pullback over any coefficient ring. -/
theorem boundarySectionsMap_adjacent_ringHom (m : ℕ) :
    boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) =
      SectionGradedLinePullback.ringHom (stageRestriction A π m n h)
        (adjacentBoundaryLineIso A π m n h) := by
  have hf : (stageSystem A π n h).map (homOfLE (Nat.le_succ m)) =
      stageRestriction A π m n h := Functor.ofSequence_map_homOfLE_succ _ m
  have he : ((Scheme.Modules.pullback
      ((stageSystem A π n h).map (homOfLE (Nat.le_succ m)))).obj
        (boundaryLine A π (m + 1) n h) ≅ boundaryLine A π m n h) =
      ((Scheme.Modules.pullback (stageRestriction A π m n h)).obj
        (boundaryLine A π (m + 1) n h) ≅ boundaryLine A π m n h) := by rw [hf]
  exact SectionGradedLinePullback.ringHom_transport hf he
    (boundaryLineSystemIso A π n h (homOfLE (Nat.le_succ m)))

variable [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0)

include hne in
/-- On each actual homogeneous degree, parameter annihilation is adjacent restriction zero. -/
theorem boundaryGrade_parameter_annihilator (m d : ℕ)
    (s : grade (boundaryLine A π (m + 1) n h) ⊤ d) :
    boundaryIntegralScalars A π n h (m + 1) π * s.val = 0 ↔
      boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) s.val = 0 := by
  obtain ⟨s, ⟨t, rfl⟩⟩ := s
  have hp := boundaryIntegralScalars_power_of A π n h (m + 1) 1 d t
  rw [pow_one, pow_one] at hp
  change boundaryIntegralScalars A π n h (m + 1) π *
      of (boundaryLine A π (m + 1) n h) ⊤ d t = 0 ↔
    boundarySectionsMap A π n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine A π (m + 1) n h) ⊤ d t) = 0
  rw [hp, boundarySectionsMap_adjacent_ringHom,
    SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    have he : stageParameterSection A π (m + 1) n h • t = 0 :=
      DirectSum.of_injective d (hz.trans (map_zero (of (boundaryLine A π (m + 1) n h) ⊤ d)).symm)
    exact (boundarySections_parameter_annihilator A π hne m n h d t).mp he
  · intro hz
    have he := (boundarySections_parameter_annihilator A π hne m n h d t).mpr hz
    rw [he, map_zero]

end FLT.Mazur.PolygonArithmeticStages
