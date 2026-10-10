/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryParameterAnnihilator
public import FLT.Mazur.PolygonCompatibleDegreeLifting
public import FLT.Mazur.SectionGradedLineKernel

/-!
# Parameter multiplication in the actual graded section rings

The complete-base parameter acts by the original structural parameter on
every homogeneous section. Its annihilator on each degree is the kernel of
the specified adjacent graded-ring map, with no degree bound.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The complete-base parameter is the actual stage structural parameter in degree zero. -/
theorem boundarySeriesScalars_parameter (m : ℕ) :
    boundarySeriesScalars R n h m PowerSeries.X =
      algebraMap Γ((family R m n h).left, ⊤) (boundaryGradedSections R n h m)
        (stageParameterSection R m n h) := by
  rw [boundarySeriesScalars_stage, seriesToStage_X]
  rfl

/-- Multiplication in the stage ring is the original scalar action in every degree. -/
theorem boundarySeriesScalars_power_of (m k d : ℕ)
    (s : Piece (boundaryLine R m n h) ⊤ d) :
    boundarySeriesScalars R n h m PowerSeries.X ^ k * of (boundaryLine R m n h) ⊤ d s =
      of (boundaryLine R m n h) ⊤ d (stageParameterSection R m n h ^ k • s) := by
  rw [boundarySeriesScalars_parameter, ← map_pow, ← Algebra.smul_def, ← map_smul]

/-- The adjacent ring map is the original specified line pullback over any coefficient ring. -/
theorem boundarySectionsMap_adjacent_ringHom (m : ℕ) :
    boundarySectionsMap R n h (homOfLE (Nat.le_succ m)) =
      SectionGradedLinePullback.ringHom (stageRestriction R m n h)
        (adjacentBoundaryLineIso R m n h) := by
  have hf : (stageSystem R n h).map (homOfLE (Nat.le_succ m)) =
      stageRestriction R m n h := Functor.ofSequence_map_homOfLE_succ _ m
  have he : ((Scheme.Modules.pullback
      ((stageSystem R n h).map (homOfLE (Nat.le_succ m)))).obj
        (boundaryLine R (m + 1) n h) ≅ boundaryLine R m n h) =
      ((Scheme.Modules.pullback (stageRestriction R m n h)).obj
        (boundaryLine R (m + 1) n h) ≅ boundaryLine R m n h) := by rw [hf]
  exact SectionGradedLinePullback.ringHom_transport hf he
    (boundaryLineSystemIso R n h (homOfLE (Nat.le_succ m)))

variable [IsNoetherianRing R]

/-- On each actual homogeneous degree, parameter annihilation is adjacent restriction zero. -/
theorem boundaryGrade_parameter_annihilator (m d : ℕ)
    (s : grade (boundaryLine R (m + 1) n h) ⊤ d) :
    boundarySeriesScalars R n h (m + 1) PowerSeries.X * s.val = 0 ↔
      boundarySectionsMap R n h (homOfLE (Nat.le_succ m)) s.val = 0 := by
  obtain ⟨s, ⟨t, rfl⟩⟩ := s
  have hp := boundarySeriesScalars_power_of R n h (m + 1) 1 d t
  rw [pow_one, pow_one] at hp
  change boundarySeriesScalars R n h (m + 1) PowerSeries.X *
      of (boundaryLine R (m + 1) n h) ⊤ d t = 0 ↔
    boundarySectionsMap R n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine R (m + 1) n h) ⊤ d t) = 0
  rw [hp, boundarySectionsMap_adjacent_ringHom,
    SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    have he : stageParameterSection R (m + 1) n h • t = 0 :=
      DirectSum.of_injective d (hz.trans (map_zero (of (boundaryLine R (m + 1) n h) ⊤ d)).symm)
    exact (boundarySections_parameter_annihilator R m n h d t).mp he
  · intro hz
    have he := (boundarySections_parameter_annihilator R m n h d t).mpr hz
    rw [he, map_zero]

end FLT.Mazur.PolygonInfinitesimalStages
