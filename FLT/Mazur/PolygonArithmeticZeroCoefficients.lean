/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AdicFiniteGenerationLifting
public import FLT.Mazur.PolygonArithmeticDegreeComplete

/-!
# Complete coefficients in the actual compatible degree zero

Structural coefficients lift all closed global functions. Adic separation
and completeness of the coefficient ring lift this to the compatible
degree-zero module. The retained marking detects coefficients injectively.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The original complete-base scalar action, with its degree-zero membership retained. -/
def compatibleZeroScalars : A →ₗ[A] compatibleSectionDegree A π n h 0 :=
  LinearMap.toSpanSingleton _ _ ⟨1, compatibleSectionDegree_one A π n h⟩

/-- Evaluating a degree-zero coefficient is the original structural coefficient at that stage. -/
theorem compatibleZeroScalars_eval (m : ℕ) (r : A) :
    compatibleEval A π n h m (compatibleZeroScalars A π n h r).val =
      boundaryIntegralScalars A π n h m r := by
  change compatibleEval A π n h m (r • (1 : CompatibleSections A π n h)) = _
  rw [Algebra.smul_def, mul_one, compatibleEval_algebraMap]

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

include hne hgen in
/-- Every stage evaluation of a degree-zero section is a structural coefficient. -/
theorem compatibleZeroScalars_stage_surjective (m : ℕ)
    (s : compatibleSectionDegree A π n h 0) : ∃ r : A,
      compatibleDegreeEval A π n h m 0 (compatibleZeroScalars A π n h r) =
        compatibleDegreeEval A π n h m 0 s := by
  obtain ⟨u, hu⟩ := s.property m
  obtain ⟨a, ha⟩ := stageScalars_surjective A π n h hgen hne m u
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨r, Subtype.ext ?_⟩
  change compatibleEval A π n h m (compatibleZeroScalars A π n h r).val = _
  rw [compatibleZeroScalars_eval, boundaryIntegralScalars_stage, hr]
  exact (congrArg (SectionGradedSum.of (boundaryLine A π m n h) ⊤ 0) ha).trans hu

variable [IsAdicComplete (ideal A π) A]

include hne hgen in
/-- All compatible degree-zero sections are original complete-base coefficients. -/
theorem compatibleZeroScalars_surjective : Function.Surjective (compatibleZeroScalars A π n h) := by
  let _ : IsHausdorff (ideal A π) (compatibleSectionDegree A π n h 0) := by
    simpa only [compatibleVeroneseDegree, Nat.mul_zero] using
      exactVeroneseDegree_hausdorff A π hne hgen n h 0
  apply surjective_of_mkQ_comp_surjective (I := ideal A π)
  intro x
  obtain ⟨s, rfl⟩ := (ideal A π • (⊤ : Submodule (A)
    (compatibleSectionDegree A π n h 0))).mkQ_surjective x
  obtain ⟨r, hr⟩ := compatibleZeroScalars_stage_surjective A π n h hne hgen 0 s
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  have hk : LinearMap.ker (compatibleDegreeEval A π n h 0 0) =
      ideal A π • (⊤ : Submodule (A) (compatibleSectionDegree A π n h 0)) := by
    simpa only [compatibleVeroneseDegree, Nat.mul_zero, Nat.zero_add, pow_one] using
      exactVeroneseDegree_ker A π hne hgen n h 0 0
  rw [← hk, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact hr

omit [NeZero n] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] in
/-- The retained marking and separated coefficient ring detect the complete coefficient uniquely. -/
theorem compatibleZeroScalars_injective : Function.Injective (compatibleZeroScalars A π n h) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro r hr
  apply IsHausdorff.haus' (I := ideal A π)
  intro m
  cases m with
  | zero => simpa only [pow_zero, one_smul] using SModEq.top
  | succ m =>
    have he := congrArg (fun s : compatibleSectionDegree A π n h 0 ↦
      compatibleEval A π n h m s.val) hr
    rw [compatibleZeroScalars_eval] at he
    have hz : boundaryIntegralScalars A π n h m r = 0 := he.trans (map_zero _)
    rw [boundaryIntegralScalars_stage] at hz
    have hz' : stageScalars A π m n h (Ideal.Quotient.mk (ideal A π ^ (m + 1)) r) = 0 :=
      DirectSum.of_injective 0 (hz.trans (map_zero _).symm)
    have hc : Ideal.Quotient.mk (ideal A π ^ (m + 1)) r = 0 :=
      stageScalars_injective A π n h m (hz'.trans (map_zero _).symm)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hc

/-- The complete coefficient ring is the actual compatible degree-zero module. -/
def compatibleZeroCoefficientEquiv :
    A ≃ₗ[A] compatibleSectionDegree A π n h 0 :=
  LinearEquiv.ofBijective (compatibleZeroScalars A π n h)
    ⟨compatibleZeroScalars_injective A π n h, compatibleZeroScalars_surjective A π n h hne hgen⟩

/-- The coefficient comparison preserves all original structural evaluations. -/
theorem compatibleZeroCoefficientEquiv_eval (m : ℕ) (r : A) :
    compatibleEval A π n h m (compatibleZeroCoefficientEquiv A π n h hne hgen r).val =
      boundaryIntegralScalars A π n h m r := compatibleZeroScalars_eval A π n h m r

end FLT.Mazur.PolygonArithmeticStages
