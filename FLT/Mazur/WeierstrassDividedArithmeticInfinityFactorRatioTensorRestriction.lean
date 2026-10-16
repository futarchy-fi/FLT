/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInfinityFactorRatioRestriction
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioLabeledMaps
public import FLT.Mazur.TensorSpectrumExt

/-!
# Full infinity quotient squares on the original arithmetic tensor atlas

Both original tensor projections identify the whole restriction. Transport then
gives the infinity label its original complete arithmetic atlas square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R) (m : ℕ) (W : WeierstrassCurve R)
local notation "Q₁" => Quotient R π (m + 1)
local notation "e₀" => Iso.hom (arithmeticInfinityTensorIso π m W)
local notation "e₁" => Iso.hom (arithmeticInfinityTensorIso π (m + 1) W)
attribute [local irreducible] arithmeticInfinityTensorIso arithmeticChartRestriction
  chartCoefficientMorphism chartStructure

/-- Both original projections identify the full infinity tensor restriction square. -/
@[reassoc] theorem arithmeticInfinityTensorIso_restriction :
    arithmeticChartRestriction R π m W 1 ≫ e₁ =
      e₀ ≫ TensorCoefficientMap.spectrum (restriction R π m) := by
  apply TensorOpenChart.spectrum_hom_ext
  · rw [Category.assoc, arithmeticInfinityTensorIso_structure,
      arithmeticChartRestriction_structure, Category.assoc,
      TensorCoefficientMap.spectrum_structure, ← Category.assoc,
      arithmeticInfinityTensorIso_structure]
    rfl
  · rw [Category.assoc, arithmeticInfinityTensorIso_projection,
      arithmeticChartRestriction_projection, Category.assoc,
      TensorCoefficientMap.spectrum_projection, arithmeticInfinityTensorIso_projection]

variable (s b3 b4 b6 : R) (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆) (k : ℕ)
attribute [local irreducible] arithmeticFactorRatioTensorInfinityMap
  arithmeticFactorRatioInfinityPolygonMap arithmeticFactorRatioPolygonRestriction

/-- The complete infinity tensor comparison retains its actual consecutive quotient square. -/
@[reassoc] theorem arithmeticFactorRatioTensorInfinityMap_restriction :
    arithmeticFactorRatioTensorInfinityMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 h3a h4a h6a k ≫
        arithmeticFactorRatioPolygonRestriction π m W s ha hs k =
      TensorCoefficientMap.spectrum (restriction R π m) ≫
        arithmeticFactorRatioTensorInfinityMap π (m + 1) W s b3 b4 b6
          ha hs h2 h3 h4 h6 h3a h4a h6a k := by
  apply (cancel_epi e₀).mp
  rw [arithmeticFactorRatioTensorInfinityMap_transport_assoc,
    arithmeticFactorRatioInfinityPolygonMap_restriction,
    ← arithmeticInfinityTensorIso_restriction_assoc,
    arithmeticFactorRatioTensorInfinityMap_transport]

variable [IsDomain R] [IsBezout R] {π W} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (hk : k ≤ n)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

omit [IsBezout R] in
/-- The full original infinity atlas label commutes with its unchanged arithmetic restriction. -/
@[reassoc] theorem arithmeticFactorRatioLabeledInfinityMap_restriction :
    arithmeticFactorRatioLabeledInfinityMap data H hπ m k hk ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ start) H.a1_unit H.scale_div k =
      arithmeticLabeledAtlasRestriction hπ data H m k hk .infinity ≫
        arithmeticFactorRatioLabeledInfinityMap data H hπ (m + 1) k hk := by
  unfold arithmeticFactorRatioLabeledInfinityMap
  exact arithmeticFactorRatioTensorInfinityMap_restriction ..

end FLT.Mazur.WeierstrassDividedDepth
