/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFiniteGenerationLifting
public import FLT.Mazur.PolygonVeroneseDegreeComplete

/-!
# Complete coefficients in the actual compatible degree zero

Structural coefficients lift all closed global functions. Adic separation
and completeness of the coefficient ring lift this to the compatible
degree-zero module. The retained marking detects coefficients injectively.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The original complete-base scalar action, with its degree-zero membership retained. -/
def compatibleZeroScalars : PowerSeries K →ₗ[PowerSeries K] compatibleSectionDegree K n h 0 :=
  LinearMap.toSpanSingleton _ _ ⟨1, compatibleSectionDegree_one K n h⟩

/-- Evaluating a degree-zero coefficient is the original structural coefficient at that stage. -/
theorem compatibleZeroScalars_eval (m : ℕ) (r : PowerSeries K) :
    compatibleEval K n h m (compatibleZeroScalars K n h r).val =
      boundarySeriesScalars K n h m r := by
  change compatibleEval K n h m (r • (1 : CompatibleSections K n h)) = _
  rw [Algebra.smul_def, mul_one, compatibleEval_algebraMap]

variable [NeZero n]

/-- Every stage evaluation of a degree-zero section is a structural coefficient. -/
theorem compatibleZeroScalars_stage_surjective (m : ℕ)
    (s : compatibleSectionDegree K n h 0) : ∃ r : PowerSeries K,
      compatibleDegreeEval K n h m 0 (compatibleZeroScalars K n h r) =
        compatibleDegreeEval K n h m 0 s := by
  obtain ⟨u, hu⟩ := s.property m
  obtain ⟨a, ha⟩ := stageScalars_surjective K n h m u
  obtain ⟨r, hr⟩ := seriesToStage_surjective K m a
  refine ⟨r, Subtype.ext ?_⟩
  change compatibleEval K n h m (compatibleZeroScalars K n h r).val = _
  rw [compatibleZeroScalars_eval, boundarySeriesScalars_stage, hr]
  exact (congrArg (SectionGradedSum.of (boundaryLine K m n h) ⊤ 0) ha).trans hu

/-- All compatible degree-zero sections are original complete-base coefficients. -/
theorem compatibleZeroScalars_surjective : Function.Surjective (compatibleZeroScalars K n h) := by
  let _ : IsHausdorff (parameterIdeal K) (compatibleSectionDegree K n h 0) := by
    simpa only [compatibleVeroneseDegree, Nat.mul_zero] using
      exactVeroneseDegree_hausdorff K n h 0
  apply surjective_of_mkQ_comp_surjective (I := parameterIdeal K)
  intro x
  obtain ⟨s, rfl⟩ := (parameterIdeal K • (⊤ : Submodule (PowerSeries K)
    (compatibleSectionDegree K n h 0))).mkQ_surjective x
  obtain ⟨r, hr⟩ := compatibleZeroScalars_stage_surjective K n h 0 s
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  have hk : LinearMap.ker (compatibleDegreeEval K n h 0 0) =
      parameterIdeal K • (⊤ : Submodule (PowerSeries K) (compatibleSectionDegree K n h 0)) := by
    simpa only [compatibleVeroneseDegree, Nat.mul_zero, Nat.zero_add, pow_one] using
      exactVeroneseDegree_ker K n h 0 0
  rw [← hk, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact hr

omit [NeZero n] in
/-- The retained marking and separated coefficient ring detect the complete coefficient uniquely. -/
theorem compatibleZeroScalars_injective : Function.Injective (compatibleZeroScalars K n h) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro r hr
  apply IsHausdorff.haus' (I := parameterIdeal K)
  intro m
  cases m with
  | zero => simpa only [pow_zero, one_smul] using SModEq.top
  | succ m =>
    have he := congrArg (fun s : compatibleSectionDegree K n h 0 ↦
      compatibleEval K n h m s.val) hr
    rw [compatibleZeroScalars_eval] at he
    have hz : boundarySeriesScalars K n h m r = 0 := he.trans (map_zero _)
    rw [boundarySeriesScalars_stage] at hz
    have hz' : stageScalars K m n h (seriesToStage K m r) = 0 :=
      DirectSum.of_injective 0 (hz.trans (map_zero _).symm)
    have hc : seriesToStage K m r = 0 :=
      stageScalars_injective K n h m (hz'.trans (map_zero _).symm)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, ← seriesToStage_ker, RingHom.mem_ker]
    exact hc

/-- The complete coefficient ring is the actual compatible degree-zero module. -/
def compatibleZeroCoefficientEquiv :
    PowerSeries K ≃ₗ[PowerSeries K] compatibleSectionDegree K n h 0 :=
  LinearEquiv.ofBijective (compatibleZeroScalars K n h)
    ⟨compatibleZeroScalars_injective K n h, compatibleZeroScalars_surjective K n h⟩

/-- The coefficient comparison preserves all original structural evaluations. -/
theorem compatibleZeroCoefficientEquiv_eval (m : ℕ) (r : PowerSeries K) :
    compatibleEval K n h m (compatibleZeroCoefficientEquiv K n h r).val =
      boundarySeriesScalars K n h m r := compatibleZeroScalars_eval K n h m r

end FLT.Mazur.PolygonInfinitesimalStages
