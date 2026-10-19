/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegationContraction
public import FLT.Mazur.WeierstrassModificationXReflectionContraction
public import FLT.Mazur.WeierstrassGlobalModificationContractionFlatExt

/-!
# Negation on the entire two-chart modification

The original divided and incidence involutions glue by uniqueness after the
original contraction. The construction includes every exceptional point and
retains both exact chart maps; no group law is assumed on the modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
local notation "M" => modification W s b3 b4 b6
local notation "c" => contraction W s b3 b4 b6 h3 h4 h6
local notation "l" => WeierstrassGlobalModification.localChart W s b3 b4 b6 h3 h4 h6 hs
local notation "N" => (initialReflectionIso W s b3 b4 b6).hom
local notation "D" => (WeierstrassDilatation.negationIso W s b3 b4 b6).hom
local notation "xj" => xChart W s b3 b4 b6
local notation "dj" => dividedChart W s b3 b4 b6

include h3 h4 h6 hs in
/-- The complete chart involutions agree on the actual gluing overlap. -/
theorem negation_chart_overlap :
    xOpenInclusion W s b3 b4 b6 ≫ (N ≫ xj) =
      overlapToDivided W s b3 b4 b6 ≫ (D ≫ dj) := by
  apply (cancel_mono l).mp
  symm
  apply WeierstrassGlobalModification.contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs
    ((xOpenInclusion W s b3 b4 b6 ≫ (N ≫ xj)) ≫ l)
  simp only [Category.assoc, WeierstrassGlobalModification.localChart_contraction,
    xChart_contraction, dividedChart_contraction, initialReflectionIso_toCurve,
    WeierstrassDilatation.negationIso_toCurve]
  simpa only [Category.assoc, xChart_contraction_assoc, dividedChart_contraction_assoc] using
    congrArg (· ≫ c ≫ WeierstrassIntegralChart.integralCurveNegation W)
      (chart_overlap W s b3 b4 b6).symm

/-- The full local equation modification has its actual integral negative morphism. -/
def modificationNegation : M ⟶ M :=
  pushout.desc (N ≫ xj) (D ≫ dj) (negation_chart_overlap W s b3 b4 b6 h3 h4 h6 hs)

/-- Negation retains the original reflection on the full incidence chart. -/
@[reassoc] theorem xChart_modificationNegation :
    xj ≫ modificationNegation W s b3 b4 b6 h3 h4 h6 hs = N ≫ xj :=
  pushout.inl_desc _ _ _

/-- Negation retains the divided inverse on the whole divided chart. -/
@[reassoc] theorem dividedChart_modificationNegation :
    dj ≫ modificationNegation W s b3 b4 b6 h3 h4 h6 hs = D ≫ dj :=
  pushout.inr_desc _ _ _

/-- The glued negative contracts to the exact original global cubic negative. -/
@[reassoc] theorem modificationNegation_contraction :
    modificationNegation W s b3 b4 b6 h3 h4 h6 hs ≫ c =
      c ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  apply pushout.hom_ext
  · change xj ≫ _ = xj ≫ _
    simp only [xChart_modificationNegation_assoc,
      xChart_contraction, xChart_contraction_assoc, initialReflectionIso_toCurve]
  · change dj ≫ _ = dj ≫ _
    simp only [dividedChart_modificationNegation_assoc,
      dividedChart_contraction, dividedChart_contraction_assoc,
      WeierstrassDilatation.negationIso_toCurve]

/-- The glued negative retains the full original affine contraction as well. -/
@[reassoc] theorem modificationNegation_affineContraction :
    modificationNegation W s b3 b4 b6 h3 h4 h6 hs ≫
        affineContraction W s b3 b4 b6 h3 h4 h6 =
      affineContraction W s b3 b4 b6 h3 h4 h6 ≫
        Spec.map (CommRingCat.ofHom (WeierstrassIntegralChart.affineNegation W).toRingHom) := by
  apply (cancel_mono (WeierstrassIntegralChart.integralCurveChart W 2)).mp
  rw [Category.assoc, affineContraction_toCurve, modificationNegation_contraction,
    Category.assoc, ← WeierstrassIntegralChart.integralCurveChart_negation_affine,
    affineContraction_toCurve_assoc]

/-- The complete local negative preserves the original coefficient map. -/
@[reassoc] theorem modificationNegation_structure :
    modificationNegation W s b3 b4 b6 h3 h4 h6 hs ≫ c ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      c ≫ WeierstrassIntegralChart.integralCurveStructure W := by
  rw [modificationNegation_contraction_assoc,
    WeierstrassIntegralChart.integralCurveNegation_structure]

/-- Squaring the whole local negative fixes every exceptional and original point. -/
@[reassoc] theorem modificationNegation_comp :
    modificationNegation W s b3 b4 b6 h3 h4 h6 hs ≫
      modificationNegation W s b3 b4 b6 h3 h4 h6 hs = 𝟙 M := by
  apply pushout.hom_ext
  · change xj ≫ _ = xj ≫ _
    simp only [xChart_modificationNegation_assoc,
      xChart_modificationNegation, Category.comp_id]
    change N ≫ (initialReflectionIso W s b3 b4 b6).inv ≫ xj = xj
    exact Iso.hom_inv_id_assoc _ _
  · change dj ≫ _ = dj ≫ _
    simp only [dividedChart_modificationNegation_assoc,
      dividedChart_modificationNegation, Category.comp_id]
    change D ≫ (WeierstrassDilatation.negationIso W s b3 b4 b6).inv ≫ dj = dj
    exact Iso.hom_inv_id_assoc _ _

/-- The entire actual local modification carries the constructed negation isomorphism. -/
def modificationNegationIso : M ≅ M where
  hom := modificationNegation W s b3 b4 b6 h3 h4 h6 hs
  inv := modificationNegation W s b3 b4 b6 h3 h4 h6 hs
  hom_inv_id := modificationNegation_comp W s b3 b4 b6 h3 h4 h6 hs
  inv_hom_id := modificationNegation_comp W s b3 b4 b6 h3 h4 h6 hs

end FLT.Mazur.WeierstrassModificationX
