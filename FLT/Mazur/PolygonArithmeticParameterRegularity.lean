/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticGradedParameter

/-!
# Parameter regularity and separation of compatible homogeneous sections

The original arithmetic stage annihilator calculation makes multiplication by the actual
arithmetic parameter injective in each compatible degree and hence in
the finite-degree-support algebra. Its parameter-adic filtration is separated.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (n : ℕ) (h : 2 ≤ n)

include hne in
/-- A compatible homogeneous section killed by the parameter is zero in every stage. -/
theorem compatibleDegree_parameter_eq_zero (d : ℕ) (s : compatibleSectionDegree A π n h d)
    (hs : π • s = 0) : s = 0 := by
  apply Subtype.ext
  apply compatibleEval_ext A π n h
  intro m
  have hz := congrArg (fun t : compatibleSectionDegree A π n h d ↦
    compatibleEval A π n h (m + 1) t.val) hs
  change compatibleEval A π n h (m + 1) (π • s.val) = _ at hz
  rw [Algebra.smul_def, map_mul, compatibleEval_algebraMap] at hz
  have hz' : boundaryIntegralScalars A π n h (m + 1) π *
      compatibleEval A π n h (m + 1) s.val = 0 := hz.trans (map_zero _)
  have he := (boundaryGrade_parameter_annihilator A π n h hne m d
    ⟨compatibleEval A π n h (m + 1) s.val, s.property (m + 1)⟩).mp hz'
  have ht := DFunLike.congr_fun
    (compatibleEval_transition A π n h (homOfLE (Nat.le_succ m))) s.val
  exact ht.symm.trans (he.trans (map_zero _).symm)

include hne in
/-- Multiplication by the parameter is injective in every compatible homogeneous degree. -/
theorem compatibleDegree_parameter_injective (d : ℕ) :
    Function.Injective (fun s : compatibleSectionDegree A π n h d ↦
      π • s) := by
  intro s t he
  change π • s = π • t at he
  apply sub_eq_zero.mp
  apply compatibleDegree_parameter_eq_zero A π hne n h d
  rw [smul_sub, he, sub_self]

include hne in
/-- The actual degreewise compatible algebra has no parameter torsion. -/
theorem compatibleGraded_parameter_eq_zero (s : CompatibleGradedSections A π n h)
    (hs : π • s = 0) : s = 0 := by
  apply DFinsupp.ext
  intro d
  apply compatibleDegree_parameter_eq_zero A π hne n h d
  have he := congrArg (fun t : CompatibleGradedSections A π n h ↦ t d) hs
  exact he

omit [IsNoetherianRing A] [IsDomain A] in
/-- The actual parameter-adic filtration on the constructed graded algebra is separated. -/
theorem compatibleParameterIdeal_separated :
    (⨅ m : ℕ, compatibleParameterIdeal A π n h ^ (m + 1)) = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  have hz : s = 0 := compatibleGradedEval_jointly_injective A π n h (fun m ↦ by
    rw [map_zero]
    exact compatibleParameterIdeal_le_ker A π n h m
      ((iInf_le (fun a : ℕ ↦ compatibleParameterIdeal A π n h ^ (a + 1)) m) hs))
  exact hz

end FLT.Mazur.PolygonArithmeticStages
