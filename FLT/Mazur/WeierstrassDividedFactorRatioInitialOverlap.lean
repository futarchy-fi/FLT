/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioPolygonMaps
public import FLT.Mazur.WeierstrassModificationXNodeOverlapFactorRatioBoundary

/-!
# Exact gluing of corrected full initial charts at arithmetic order

The original overlap restrictions have exactly reciprocal corrected parameters.
Their actual adjacent labels therefore glue in the full normalized polygon.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (τ : R) [Fact (IsNilpotent τ)] (k : ℕ)

/-- The actual adjacent labels identify reciprocal parameters for the whole smoothing. -/
@[reassoc] theorem initialPolygonLabel_full_opposite_boundary :
    (edgeInversion R).hom ≫ rightBranchOpen R τ ≫ (branchSwapIso R τ).hom ≫
      PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k true) =
        rightBranchOpen R τ ≫
          PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega)
            (initialPolygonIndex k false) := by
  rw [rightBranchOpen_branchSwapIso_assoc, PolygonInfinitesimal.overlap,
    initialPolygonIndex_preceding]
  simp only [precedingBranch, ← Category.assoc]
  rw [show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
    (edgeInversion R).hom_inv_id, Category.id_comp]

variable (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s : R)
  (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "F" => factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3

/-- Both actual original node-overlap legs agree in the complete corrected arithmetic polygon. -/
@[reassoc] theorem factorRatioInitialPolygonMap_original_overlap :
    polynomialNodeOverlapInclusion W s ≫ F false =
      polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫ F true := by
  simp only [factorRatioInitialPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [polynomialFactorRatioChart_overlap_first_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3,
    polynomialFactorRatioChart_overlap_opposite_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3]
  rw [initialPolygonLabel_full_opposite_boundary]

end FLT.Mazur.WeierstrassDividedDepth
