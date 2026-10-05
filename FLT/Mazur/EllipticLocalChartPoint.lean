/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalEvaluation
public import FLT.Mazur.EllipticFormalProjective

/-!
# Every maximal-ideal parameter gives an actual E₁ point

Convergent infinity coordinates produce a nonsingular integral representative.
Its primitive reduction is infinity. Together with parameter injectivity this
gives a bijective parametrization of the actual reduction kernel.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- The evaluated local chart has a unit Z-partial and is nonsingular. -/
theorem infinityEvaluation_nonsingular (t : A) (ht : t ∈ maximalIdeal A) :
    W.toProjective.Nonsingular ![t, -1, infinityEvaluation A W t ht] := by
  constructor
  · apply (FormalInfinity.projective_equation_iff W _ _).mpr
    exact infinityEvaluation_equation A W t ht
  · right; right
    apply IsUnit.ne_zero
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [eval_polynomialZ]
    have hs := (residue_eq_zero_iff _).mpr (infinityEvaluation_mem A W t ht)
    have ht0 := (residue_eq_zero_iff _).mpr ht
    simp [ht0, hs]

/-- The generic point of the convergent local chart. -/
noncomputable def localChartPoint (t : A) (ht : t ∈ maximalIdeal A) :
    (W.map (algebraMap A K)).toProjective.Point :=
  ⟨(nonsingularLift_iff _).mpr ((map_nonsingular W
    (show Function.Injective (algebraMap A K) from Subtype.val_injective) _).mpr
    (infinityEvaluation_nonsingular A W t ht))⟩

/-- The local chart point lies in the actual reduction kernel. -/
theorem localChartPoint_mem (t : A) (ht : t ∈ maximalIdeal A) :
    localChartPoint A W t ht ∈ ellipticE1 A W := by
  let v : PrimitiveLift A (localChartPoint A W t ht).point :=
    { coords := ![t, -1, infinityEvaluation A W t ht]
      primitive := ⟨1, by simp⟩
      represents := rfl }
  apply (infinityReduction_iff_residue_z A W v).mpr
  exact (residue_eq_zero_iff _).mpr (infinityEvaluation_mem A W t ht)

/-- A maximal-ideal parameter determines an actual point of E₁. -/
noncomputable def localE1Point (t : A) (ht : t ∈ maximalIdeal A) : ellipticE1 A W :=
  ⟨localChartPoint A W t ht, localChartPoint_mem A W t ht⟩

/-- Normalization recovers the chosen parameter. -/
@[simp] theorem infinityParameter_localE1Point (t : A) (ht : t ∈ maximalIdeal A) :
    infinityParameter A W (localE1Point A W t ht) = t := by
  have hp := ellipticE1_point_eq_evaluation A W (localE1Point A W t ht)
  obtain ⟨u, hu⟩ := Quotient.exact hp
  have hy := congrFun hu 1
  have hx := congrFun hu 0
  have hu1 : (u : K) = 1 := by
    simpa [localE1Point, localChartPoint, Function.comp_apply, Units.smul_def] using hy
  apply Subtype.ext
  simpa [localE1Point, localChartPoint, Function.comp_apply, Units.smul_def, hu1] using hx

/-- Evaluation reconstructs the original E₁ point. -/
@[simp] theorem localE1Point_infinityParameter (P : ellipticE1 A W) :
    localE1Point A W (infinityParameter A W P) (infinityParameter_mem A W P) = P := by
  apply infinityParameter_injective A W
  exact infinityParameter_localE1Point A W _ _

/-- The actual reduction kernel is in bijection with maximal-ideal parameters. -/
noncomputable def infinityParameterEquiv : ellipticE1 A W ≃ maximalIdeal A where
  toFun P := ⟨infinityParameter A W P, infinityParameter_mem A W P⟩
  invFun t := localE1Point A W t.val t.property
  left_inv := localE1Point_infinityParameter A W
  right_inv t := Subtype.ext (infinityParameter_localE1Point A W t.val t.property)

end FLT.Mazur
