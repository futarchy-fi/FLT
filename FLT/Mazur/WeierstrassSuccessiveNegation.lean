/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNegationOverlap

/-!
# Constructed negation on the entire local successor

Glue the two explicit chart negatives along their constructed overlap negative.
The involution retains the entire preceding divided contraction, including
exceptional points and scheme structure, over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option quotPrecheck false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "M" => modification W s π b3 b4 b6
local notation "c" => contraction W s π b3 b4 b6
local notation "N" => (negationIso W s π b3 b4 b6).hom
local notation "D" => (WeierstrassDilatation.negationIso W (s * π) b3 b4 b6).hom
local notation "xj" => xChart W s π b3 b4 b6
local notation "dj" => dividedChart W s π b3 b4 b6

/-- The actual successor negative, defined on the whole local modification. -/
def modificationNegation : M ⟶ M :=
  pushout.desc (N ≫ xj) (D ≫ dj) (negation_chart_overlap W s π b3 b4 b6)

/-- Negation retains the complete three-generator incidence chart. -/
@[reassoc] theorem xChart_modificationNegation :
    xj ≫ modificationNegation W s π b3 b4 b6 = N ≫ xj := pushout.inl_desc _ _ _

/-- Negation retains the entire deeper divided chart. -/
@[reassoc] theorem dividedChart_modificationNegation :
    dj ≫ modificationNegation W s π b3 b4 b6 = D ≫ dj := pushout.inr_desc _ _ _

/-- The actual successor contraction commutes with the constructed negatives. -/
@[reassoc] theorem modificationNegation_contraction :
    modificationNegation W s π b3 b4 b6 ≫ c = c ≫
      (WeierstrassDilatation.negationIso W s (π * b3) (π * b4) (π ^ 2 * b6)).hom := by
  apply pushout.hom_ext
  · change xj ≫ _ = xj ≫ _
    simp only [xChart_modificationNegation_assoc, xChart_contraction,
      xChart_contraction_assoc, negationIso_toDivided]
  · change dj ≫ _ = dj ≫ _
    simp only [dividedChart_modificationNegation_assoc, dividedChart_contraction,
      dividedChart_contraction_assoc, dividedNegation_toPrevious]

/-- Squaring the constructed negative fixes every point and regular function. -/
@[reassoc] theorem modificationNegation_comp :
    modificationNegation W s π b3 b4 b6 ≫ modificationNegation W s π b3 b4 b6 = 𝟙 M := by
  apply pushout.hom_ext
  · change xj ≫ _ = xj ≫ _
    simp only [xChart_modificationNegation_assoc, xChart_modificationNegation, Category.comp_id]
    change N ≫ (negationIso W s π b3 b4 b6).inv ≫ xj = xj
    exact Iso.hom_inv_id_assoc _ _
  · change dj ≫ _ = dj ≫ _
    simp only [dividedChart_modificationNegation_assoc,
      dividedChart_modificationNegation, Category.comp_id]
    change D ≫ (WeierstrassDilatation.negationIso W (s * π) b3 b4 b6).inv ≫ dj = dj
    exact Iso.hom_inv_id_assoc _ _

/-- The whole actual local successor has an integral negation automorphism. -/
def modificationNegationIso : M ≅ M where
  hom := modificationNegation W s π b3 b4 b6
  inv := modificationNegation W s π b3 b4 b6
  hom_inv_id := modificationNegation_comp W s π b3 b4 b6
  inv_hom_id := modificationNegation_comp W s π b3 b4 b6

/-- The local successor negative retains the chosen original projective cubic. -/
@[reassoc] theorem modificationNegation_toCurve
    (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) :
    modificationNegation W s π b3 b4 b6 ≫ contractionToCurve W s π b3 b4 b6 h3 h4 h6 =
      contractionToCurve W s π b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W := by
  rw [contractionToCurve, modificationNegation_contraction_assoc,
    WeierstrassDilatation.negationIso_toCurve]
  simp only [Category.assoc]

/-- Negation fixes the exact original integral coefficient morphism. -/
@[reassoc] theorem modificationNegation_structure
    (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) :
    modificationNegation W s π b3 b4 b6 ≫ contractionToCurve W s π b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      contractionToCurve W s π b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveStructure W := by
  rw [modificationNegation_toCurve_assoc,
    WeierstrassIntegralChart.integralCurveNegation_structure]

end FLT.Mazur.WeierstrassSuccessiveX
