/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioOverlapTorus
public import FLT.Mazur.WeierstrassDividedArithmeticInfinityFactorRatioRestriction

/-!
# The complete arithmetic infinity parameter respects quotient maps

Cancel the actual open cyclic boundary in the full polygon square. This keeps
both independently constructed canonical roots and the original cubic restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassIntegralChart
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆)
local notation "Q" => Quotient R π
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W ha s π k
local notation "F" => fun k ↦ arithmeticFullInfinityRatioParameter π k W s b3 b4 b6
  ha h2 h3 h4 h6 h3a h4a h6a
local notation "c" => (Spec.map
  (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap (AlgHom.toRingHom (restriction R π m)))))

include hs in
/-- Every Laurent function of the full infinity chart follows the original quotient arrow. -/
@[reassoc] theorem arithmeticFullInfinityRatioParameter_restriction :
    arithmeticChartRestriction R π m W 1 ≫ F (m + 1) = F m ≫ c := by
  let _ : Fact (IsNilpotent (τ m)) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs⟩
  let _ : Fact (IsNilpotent (τ (m + 1))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  let B := rightBranchOpen (Q (m + 1)) (τ (m + 1)) ≫
    PolygonInfinitesimal.chart (Q (m + 1)) (τ (m + 1)) 3 (by omega)
      (initialPolygonIndex 0 false)
  apply (cancel_mono B).mp
  have h := arithmeticFactorRatioInfinityPolygonMap_restriction π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 h3a h4a h6a 0
  change (F m ≫ rightBranchOpen (Q m) (τ m) ≫
    PolygonInfinitesimal.chart (Q m) (τ m) 3 (by omega) (initialPolygonIndex 0 false)) ≫
      arithmeticFactorRatioPolygonRestriction π m W s ha hs 0 =
        arithmeticChartRestriction R π m W 1 ≫ F (m + 1) ≫ B at h
  rw [arithmeticFactorRatioPolygonRestriction, Category.assoc, Category.assoc,
    PolygonInfinitesimal.chart_parameterProjection,
    factorRatioRightBranch_coefficient_assoc] at h
  simpa only [B, Category.assoc] using h.symm

/-- The complete infinity parameter preserves the actual arithmetic coefficient ring. -/
@[reassoc] theorem arithmeticFullInfinityRatioParameter_base :
    F m ≫ Spec.map (CommRingCat.ofHom (algebraMap (Q m)
      (LaurentPolynomial (Q m)))) = WeierstrassIntegralChart.chartStructure
      (W.map (algebraMap R (Q m))) 1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (LaurentUnitPoints.evalUnit _).commutes)

end FLT.Mazur.WeierstrassDividedDepth
