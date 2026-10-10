/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryGradedParameter

/-!
# Parameter regularity and separation of compatible homogeneous sections

The stage annihilator calculation makes multiplication by the actual
complete-base parameter injective in each compatible degree and hence in
the finite-degree-support algebra. Its parameter-adic filtration is separated.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (R : Type) [CommRing R] [IsNoetherianRing R] (n : ℕ) (h : 2 ≤ n)

/-- A compatible homogeneous section killed by the parameter is zero in every stage. -/
theorem compatibleDegree_parameter_eq_zero (d : ℕ) (s : compatibleSectionDegree R n h d)
    (hs : (PowerSeries.X : PowerSeries R) • s = 0) : s = 0 := by
  apply Subtype.ext
  apply compatibleEval_ext R n h
  intro m
  have hz := congrArg (fun t : compatibleSectionDegree R n h d ↦
    compatibleEval R n h (m + 1) t.val) hs
  change compatibleEval R n h (m + 1) (PowerSeries.X • s.val) = _ at hz
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap] at hz
  have hz' : boundarySeriesScalars R n h (m + 1) PowerSeries.X *
      compatibleEval R n h (m + 1) s.val = 0 := hz.trans (map_zero _)
  have he := (boundaryGrade_parameter_annihilator R n h m d
    ⟨compatibleEval R n h (m + 1) s.val, s.property (m + 1)⟩).mp hz'
  have ht := DFunLike.congr_fun
    (compatibleEval_transition R n h (homOfLE (Nat.le_succ m))) s.val
  exact ht.symm.trans (he.trans (map_zero _).symm)

/-- Multiplication by the parameter is injective in every compatible homogeneous degree. -/
theorem compatibleDegree_parameter_injective (d : ℕ) :
    Function.Injective (fun s : compatibleSectionDegree R n h d ↦
      (PowerSeries.X : PowerSeries R) • s) := by
  intro s t he
  change (PowerSeries.X : PowerSeries R) • s = PowerSeries.X • t at he
  apply sub_eq_zero.mp
  apply compatibleDegree_parameter_eq_zero R n h d
  rw [smul_sub, he, sub_self]

/-- The actual degreewise compatible algebra has no parameter torsion. -/
theorem compatibleGraded_parameter_eq_zero (s : CompatibleGradedSections R n h)
    (hs : (PowerSeries.X : PowerSeries R) • s = 0) : s = 0 := by
  apply DFinsupp.ext
  intro d
  apply compatibleDegree_parameter_eq_zero R n h d
  have he := congrArg (fun t : CompatibleGradedSections R n h ↦ t d) hs
  exact he

omit [IsNoetherianRing R] in
/-- The actual parameter-adic filtration on the constructed graded algebra is separated. -/
theorem compatibleParameterIdeal_separated :
    (⨅ m : ℕ, compatibleParameterIdeal R n h ^ (m + 1)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  have hz : s = 0 := compatibleGradedEval_jointly_injective R n h (fun m ↦ by
    rw [map_zero]
    exact compatibleParameterIdeal_le_ker R n h m
      ((iInf_le (fun a : ℕ ↦ compatibleParameterIdeal R n h ^ (a + 1)) m) hs))
  exact hz

end FLT.Mazur.PolygonInfinitesimalStages
