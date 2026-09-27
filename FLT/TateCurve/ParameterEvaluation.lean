/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Elliptic

/-!
# Evaluation of the inverse Tate parameter series

Substitution of integral formal series commutes with evaluation on the open
unit disc. Consequently the two formal inverse identities for `jInvReverse`
hold after evaluation over every nonarchimedean local field.
-/

@[expose] public section

open scoped PowerSeries PowerSeries.WithPiTopology
open ValuativeRel
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- Integral series evaluation commutes with substitution of a series with zero constant term. -/
theorem evalInt_subst (q : K) (hq : valuation K q < 1)
    (F G : ℤ⟦X⟧) (hG : PowerSeries.constantCoeff G = 0) :
    evalInt q (PowerSeries.subst G F) = evalInt (evalInt q G) F := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup 𝒪[K] := inferInstanceAs (IsUniformAddGroup 𝒪[K].toAddSubgroup)
  have hind : Topology.IsInducing ((↑) : 𝒪[K] → K) := ⟨rfl⟩
  have hφ : Continuous (Int.castRingHom 𝒪[K]) := continuous_of_discreteTopology
  have ha : PowerSeries.HasEval (⟨q, hq.le⟩ : 𝒪[K]) :=
    hind.tendsto_nhds_iff.mpr (by simpa [Function.comp_def] using tendsto_pow_nhds_zero hq)
  have key : ∀ H : ℤ⟦X⟧,
      evalInt q H = (↑(PowerSeries.eval₂ (Int.castRingHom 𝒪[K]) ⟨q, hq.le⟩ H) : K) := by
    intro H
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def] using (PowerSeries.hasSum_eval₂ hφ ha H).map
      (Subring.subtype 𝒪[K]).toAddMonoidHom continuous_subtype_val
  rw [key]
  have hs := MvPowerSeries.eval₂_subst
    (R := ℤ) (S := ℤ) (T := 𝒪[K])
    (PowerSeries.HasSubst.of_constantCoeff_zero hG).const (PowerSeries.hasEval ha) F
  change (↑(MvPowerSeries.eval₂ (algebraMap ℤ 𝒪[K]) (fun _ : Unit ↦ ⟨q, hq.le⟩)
    (MvPowerSeries.subst (fun _ : Unit ↦ G) F)) : K) = _
  rw [hs]
  change (↑(PowerSeries.eval₂ (Int.castRingHom 𝒪[K])
    (PowerSeries.eval₂ (Int.castRingHom 𝒪[K]) ⟨q, hq.le⟩ G) F) : K) = _
  have hGev : PowerSeries.HasEval
      (PowerSeries.eval₂ (Int.castRingHom 𝒪[K]) ⟨q, hq.le⟩ G) := by
    simpa only [PowerSeries.coe_eval₂Hom] using
      (PowerSeries.HasSubst.of_constantCoeff_zero hG).hasEval.map
        (φ := PowerSeries.eval₂Hom hφ ha)
        (by simpa only [PowerSeries.coe_eval₂Hom] using PowerSeries.continuous_eval₂ hφ ha)
  have hsum := (PowerSeries.hasSum_eval₂ hφ hGev F).map
      (Subring.subtype 𝒪[K]).toAddMonoidHom continuous_subtype_val
  simpa [Function.comp_def, ← key G, evalInt] using hsum.tsum_eq.symm
/-- Evaluated inverse j-series undo each other on the open unit disc. -/
theorem evalInt_jInv_jInvReverse (q : K) (hq : valuation K q < 1) :
    evalInt (evalInt q jInvReverse) jInv = q := by
  rw [← evalInt_subst q hq _ _ constantCoeff_jInvReverse,
    jInv_subst_jInvReverse, evalInt_X]

/-- Evaluated j-series and inverse j-series also compose in the opposite order. -/
theorem evalInt_jInvReverse_jInv (q : K) (hq : valuation K q < 1) :
    evalInt (evalInt q jInv) jInvReverse = q := by
  rw [← evalInt_subst q hq _ _ constantCoeff_jInv, subst_jInvReverse, evalInt_X]

/-- The product-defined reciprocal j-series evaluated at the Tate parameter is `j⁻¹`. -/
theorem evalInt_jInv_tateParameter {j : K} (hj : 1 < valuation K j) :
    evalInt (WeierstrassCurve.tateParameter j) jInv = j⁻¹ := by
  exact evalInt_jInv_jInvReverse j⁻¹ (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj)

end TateCurve
