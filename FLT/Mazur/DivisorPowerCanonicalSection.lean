/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalComposition
public import FLT.Mazur.ModuleTensorPowerSectionInduction
public import FLT.Mazur.DivisorLineBundlePower
public import Mathlib.Tactic.IrreducibleDef
/-!
# Canonical sections under the existing divisor-power comparison

Seal the unit and addition comparisons before specializing them to ideal powers.
Their defining equalities identify them with the existing comparisons, so the
induction proves preservation for the original divisorLineBundlePowerIso.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {I J L : X.IdealSheafData}
/-- The empty-divisor comparison sealed against kernel unfolding. -/
irreducible_def divisorUnitComparison (hJ : EffectiveCartier J)
    (he : (⊤ : X.IdealSheafData) = J) : structureModule X ≅ divisorLineBundle J hJ :=
  (divisorLineBundleTopIso effectiveCartier_top).symm ≪≫
    divisorLineBundleEqIso he effectiveCartier_top hJ
/-- The sealed unit comparison preserves the canonical section. -/
lemma divisorUnitComparison_section (hJ : EffectiveCartier J)
    (he : (⊤ : X.IdealSheafData) = J) (U : X.Opens) :
    (divisorUnitComparison hJ he).hom.app U (1 : Γ(X, U)) = divisorSection hJ U := by
  rw [divisorUnitComparison_def]
  exact divisorSection_top_eq hJ he U
/-- Divisor addition and ideal transport with an opaque implementation. -/
irreducible_def divisorSumComparison (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (hL : EffectiveCartier L) (he : I * J = L) :
    ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ) ≅
      divisorLineBundle L hL :=
  divisorLineBundleSumIso hI hJ ≪≫ divisorLineBundleEqIso he (hI.mul hJ) hL
/-- The sealed sum comparison multiplies canonical sections. -/
lemma divisorSumComparison_section (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (hL : EffectiveCartier L) (he : I * J = L) (U : X.Opens) :
    (divisorSumComparison hI hJ hL he).hom.app U
      (ModuleSheafTensor.pure _ _ U (divisorSection hI U) (divisorSection hJ U)) =
        divisorSection hL U := by
  rw [divisorSumComparison_def]
  exact divisorSection_sum_eq hI hJ hL he U
/-- The degree-zero canonical section is preserved. -/
lemma powerZero_section (hI : EffectiveCartier I) (U : X.Opens) :
    (divisorUnitComparison (hI.pow 0) (by simp)).hom.app U (1 : Γ(X, U)) =
      divisorSection (hI.pow 0) U := divisorUnitComparison_section _ _ U
/-- The successor comparison preserves the pure pair of canonical sections. -/
lemma powerStep_section (hI : EffectiveCartier I) (m : ℕ) (U : X.Opens) :
    (divisorSumComparison hI (hI.pow m) (hI.pow (m + 1)) (pow_succ' I m).symm).hom.app U
      (ModuleSheafTensor.pure _ _ U (divisorSection hI U)
        (divisorSection (hI.pow m) U)) = divisorSection (hI.pow (m + 1)) U :=
  divisorSumComparison_section _ _ _ _ U
/-- The original degree-zero comparison equals its sealed presentation. -/
lemma powerIso_sealed_zero (hI : EffectiveCartier I) :
    divisorLineBundlePowerIso hI 0 = divisorUnitComparison (hI.pow 0) (by simp) :=
  (divisorLineBundlePowerIso_zero hI).trans (divisorUnitComparison_def _ _).symm
/-- The original successor comparison factors through sealed divisor addition. -/
lemma powerIso_sealed_succ (hI : EffectiveCartier I) (m : ℕ) :
    divisorLineBundlePowerIso hI (m + 1) =
      ModuleSheafTensor.congr (Iso.refl _) (divisorLineBundlePowerIso hI m) ≪≫
        divisorSumComparison hI (hI.pow m) (hI.pow (m + 1)) (pow_succ' I m).symm := by
  rw [divisorSumComparison_def, divisorLineBundlePowerIso_succ]
/-- The existing divisor-power isomorphism preserves the actual canonical section. -/
lemma divisorSection_power (hI : EffectiveCartier I) (U : X.Opens) (m : ℕ) :
    (divisorLineBundlePowerIso hI m).hom.app U
      (tensorPowerSection (divisorLineBundle I hI) U (divisorSection hI U) m) =
      divisorSection (hI.pow m) U :=
  sectionPower_induction (divisorLineBundle I hI)
    (fun k ↦ divisorLineBundle (I ^ k) (hI.pow k))
    (divisorLineBundlePowerIso hI)
    (divisorUnitComparison (hI.pow 0) (by simp))
    (fun k ↦ divisorSumComparison hI (hI.pow k) (hI.pow (k + 1)) (pow_succ' I k).symm)
    (powerIso_sealed_zero hI) (powerIso_sealed_succ hI)
    U (divisorSection hI U) (fun k ↦ divisorSection (hI.pow k) U)
    (powerZero_section hI U) (fun k ↦ powerStep_section hI k U) m
end FLT.Mazur.FCurve
