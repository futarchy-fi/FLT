/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Discriminant
public import FLT.TateCurve.ParameterEvaluation

/-!
# The j-invariant round trips for the Tate parameter

The product-defined reciprocal j-series is the reciprocal j-invariant of
the Tate equation. Evaluating the formal inverse identities recovers both
the j-invariant and the Tate parameter on their convergence domains.
-/

@[expose] public section

open scoped PowerSeries
open ValuativeRel PowerSeries
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Evaluation of the formal reciprocal j-series gives the reciprocal curve invariant. -/
theorem evalInt_jInv {q : K} (hq : valuation K q < 1)
    [(WeierstrassCurve.tateCurve q).IsElliptic] :
    evalInt q jInv = (WeierstrassCurve.tateCurve q).j⁻¹ := by
  have hmap4 : evalInt q c₄Formal = (WeierstrassCurve.tateCurve q).c₄ := by
    rw [← formalCurve_c₄]
    exact (formalCurve.map_c₄ (evalIntHom q hq)).symm.trans
      (congrArg WeierstrassCurve.c₄ (map_formalCurve q hq))
  have hmapΔ : evalInt q ΔFormal = (WeierstrassCurve.tateCurve q).Δ := by
    rw [← formalCurve_Δ]
    exact (formalCurve.map_Δ (evalIntHom q hq)).symm.trans
      (congrArg WeierstrassCurve.Δ (map_formalCurve q hq))
  have hunit : constantCoeff (c₄Formal ^ 3) = (1 : ℤ) := by
    simp [c₄Formal, sInt]
  have hinv := congrArg (evalIntHom q hq) (mul_invOfUnit (c₄Formal ^ 3) 1 hunit)
  change evalInt q (c₄Formal ^ 3 * invOfUnit (c₄Formal ^ 3) 1) = evalInt q 1 at hinv
  rw [evalInt_mul q hq, evalInt_pow q hq, hmap4] at hinv
  have hi : evalInt q (invOfUnit (c₄Formal ^ 3) 1) =
      ((WeierstrassCurve.tateCurve q).c₄ ^ 3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [evalInt, mul_comm] using hinv
  rw [jInv, evalInt_mul q hq, hmapΔ, hi, WeierstrassCurve.j_eq, mul_inv, inv_inv]

/-- The j-invariant recovers the argument of the Tate parameter on its convergence domain. -/
theorem j_tateCurve_tateParameter {j : K}
    (hj : 1 < valuation K j) [(WeierstrassCurve.tateCurve
      (WeierstrassCurve.tateParameter j)).IsElliptic] :
    (WeierstrassCurve.tateCurve (WeierstrassCurve.tateParameter j)).j = j := by
  have hv : valuation K j⁻¹ < 1 := by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj
  have hq : valuation K (WeierstrassCurve.tateParameter j) < 1 := by
    exact lt_of_le_of_lt (valuation_evalInt_le_pow j⁻¹ hv
      (M := 1) (F := jInvReverse) (by
        intro m hm
        have hm0 : m = 0 := by omega
        subst m
        simp))
      (by simpa using hv)
  apply inv_injective
  rw [← evalInt_jInv hq, evalInt_jInv_tateParameter hj]

/-- The Tate parameter recovers a curve parameter in the open unit disc. -/
theorem tateParameter_j_tateCurve {q : K} (hq : valuation K q < 1)
    [(WeierstrassCurve.tateCurve q).IsElliptic] :
    WeierstrassCurve.tateParameter (WeierstrassCurve.tateCurve q).j = q := by
  change evalInt (WeierstrassCurve.tateCurve q).j⁻¹ jInvReverse = q
  rw [← evalInt_jInv hq, evalInt_jInvReverse_jInv q hq]

end TateCurve
