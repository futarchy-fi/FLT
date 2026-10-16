/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioInitialAffine
public import FLT.Mazur.WeierstrassModificationXFactorRatioInfinityBoundary

/-!
# The full corrected affine polygon map on the original infinity boundary

The original D(y) restriction of the glued arithmetic affine map retains its
exact full factor-ratio parameter and original cyclic label.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "e" => polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3
local notation "P" => factorRatioOverlapParameter W s b3 b4 b6 r hr I hI hrI h3
local notation "f" => factorRatioInitialAffinePolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3

/-- The full original affine comparison has this exact boundary in its first initial label. -/
@[reassoc] theorem factorRatioInitialAffinePolygonMap_infinity_boundary :
    polynomialInitialInfinityInclusion W s b3 b4 b6 ≫ f =
      factorRatioInfinityParameter W s b3 b4 b6 r hr I hI hrI h3 ≫ rightBranchOpen R τ ≫
        PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega)
          (initialPolygonIndex k false) := by
  have hf : polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫ f =
      factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 false :=
    factorRatioInitialAffinePolygonMap_chart W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 false
  apply (cancel_epi (e).hom).mp
  rw [← Category.assoc, polynomialNodeOverlapInfinityIso_hom_inclusion,
    Category.assoc, hf]
  simp only [factorRatioInitialPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [polynomialFactorRatioChart_overlap_first_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3,
    factorRatioInfinityParameter]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
