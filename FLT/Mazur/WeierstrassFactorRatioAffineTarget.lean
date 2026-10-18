/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFactorRatioNodeTarget
public import FLT.Mazur.WeierstrassDividedFullInfinityFactorRatioMap

/-!
# Full affine and infinity factor ratios in an adjacent target pair

The actual polynomial node cover glues the complete affine map. Its original
projective transition agrees with the complete regular infinity factor ratio.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  {Y : Scheme} (c : (b : Bool) → PolygonSmoothing.chart R τ ⟶ Y)
  (hc : leftBranchOpen R τ ≫ c true = precedingBranch R τ ≫ c false)
local notation "U" => polynomialNodeOpenCover W s b3 b4 b6 r hr I hI hrI h3 ha
local notation "F" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "f" => factorRatioNodeTargetMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 c

/-- The entire original affine chart maps by gluing its actual two polynomial nodes. -/
def factorRatioAffineTargetMap : Spec (.of (WeierstrassModificationX.Coordinate W s b3 b4 b6))
    ⟶ Y :=
  (U).glueMorphisms f (polynomialNodeOpenCover_compatible W s b3 b4 b6 r hr I hI hrI h3 ha f
    (factorRatioNodeTargetMap_overlap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 c hc))

local notation "g" => factorRatioAffineTargetMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 c hc

/-- Each original whole node retains the chosen full target map after gluing. -/
@[reassoc] theorem factorRatioAffineTargetMap_chart (b : Bool) :
    (if b then G else F) ≫ g = f b := (U).ι_glueMorphisms _ _ b

/-- The full affine map keeps the exact factor ratio on the original infinity localization. -/
@[reassoc] theorem factorRatioAffineTargetMap_infinity_boundary :
    polynomialInitialInfinityInclusion W s b3 b4 b6 ≫ g =
      factorRatioInfinityParameter W s b3 b4 b6 r hr I hI hrI h3 ≫
        rightBranchOpen R τ ≫ c false := by
  have hf : F ≫ g = f false :=
    factorRatioAffineTargetMap_chart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 c hc false
  let e := polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, polynomialNodeOverlapInfinityIso_hom_inclusion,
    Category.assoc, hf]
  simp only [factorRatioNodeTargetMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [polynomialFactorRatioChart_overlap_first_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3,
    factorRatioInfinityParameter]
  simp only [e, Category.assoc, Iso.hom_inv_id_assoc]

variable (h2I : W.a₂ ∈ I) (h3I : W.a₃ ∈ I) (h4I : W.a₄ ∈ I) (h6I : W.a₆ ∈ I)

/-- The complete original infinity cubic maps to the same full target edge. -/
def factorRatioInfinityTargetMap : Spec (.of (WeierstrassIntegralChart.Coordinate W 1)) ⟶ Y :=
  infinityFactorRatioParameter W I hI h2I h3I h4I h6I s b3 r hrI h3 ≫
    rightBranchOpen R τ ≫ c false

variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

/-- The actual original projective transition commutes on its entire source. -/
@[reassoc] theorem factorRatioInfinityTargetMap_initial :
    Spec.map (CommRingCat.ofHom (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
      factorRatioInfinityTargetMap W s τ b3 r I hI hrI h3 c h2I h3I h4I h6I =
        polynomialInitialInfinityInclusion W s b3 b4 b6 ≫ g := by
  rw [factorRatioInfinityTargetMap, ← Category.assoc,
    fullInfinityFactorRatioParameter_boundary W s b3 b4 b6 h₃ h₄ h₆
      I hI h2I h3I h4I h6I r hr hrI h3,
    factorRatioAffineTargetMap_infinity_boundary]

end FLT.Mazur.WeierstrassDividedDepth
