/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFullInfinityFactorRatioMap
public import FLT.Mazur.WeierstrassInfinityFactorRatioParameterNaturality
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality

/-!
# The full infinity polygon square under coefficient change

The regular ratio passes through the actual right branch and original polygon
projection. Every Laurent function and the entire nilpotent smoothing are retained.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s τ : R) (τ' : S) (ht : f τ = τ')
  [Fact (IsNilpotent τ)] [Fact (IsNilpotent τ')] (k : ℕ)
  (b3 : R) (r : R[X]) (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (h2a : W.a₂ ∈ I) (h3a : W.a₃ ∈ I) (h4a : W.a₄ ∈ I) (h6a : W.a₆ ∈ I)

omit [Fact (IsNilpotent τ)] [Fact (IsNilpotent τ')] in
/-- The right branch follows the full coefficient substitution without coordinate inversion. -/
@[reassoc] theorem factorRatioRightBranch_coefficient :
    rightBranchOpen S τ' ≫ Spec.map (CommRingCat.ofHom (ringMap f τ τ' ht)) =
      Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) ≫
        rightBranchOpen R τ := by
  rw [← leftBranchOpen_branchSwapIso S τ', Category.assoc, branchSwapIso_ringMap,
    ← Category.assoc, leftBranchOpen_ringMap, Category.assoc, leftBranchOpen_branchSwapIso]

/-- The whole infinity comparison commutes with the actual complete polygon projection. -/
@[reassoc] theorem fullFactorRatioInfinityPolygonMap_coefficient :
    fullFactorRatioInfinityPolygonMap (W.map f) (f s) τ' k (f b3) (r.map f)
      J hJ (polynomialArithmeticIdeal_coefficient f I J hf hrI) (hf h3)
      (hf h2a) (hf h3a) (hf h4a) (hf h6a) ≫
        PolygonInfinitesimal.parameterProjection f τ τ' ht (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (chartCoefficientRingMap f W 1)) ≫
        fullFactorRatioInfinityPolygonMap W s τ k b3 r I hI hrI h3 h2a h3a h4a h6a := by
  unfold fullFactorRatioInfinityPolygonMap
  rw [Category.assoc, Category.assoc, PolygonInfinitesimal.chart_parameterProjection,
    factorRatioRightBranch_coefficient_assoc, ← Category.assoc,
    ← infinityFactorRatioParameter_coefficient, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
