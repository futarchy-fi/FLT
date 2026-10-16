/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioPolygonMaps

/-!
# Original coefficient squares at both corrected cyclic labels

The complete labeled polygon maps follow coefficient restriction with their
actual normalized smoothing and transported polynomial root.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R)
  (hτ : s = W.a₁ ^ 2 * τ) (τ' : S) (hτ' : f s = (W.map f).a₁ ^ 2 * τ') (ht : f τ = τ')
  [Fact (IsNilpotent τ)] [Fact (IsNilpotent τ')] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "F" => factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3
local notation "F'" => factorRatioInitialPolygonMap U (ha.map f) (f s) τ' hτ' k
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)

/-- Both corrected cyclic labels retain the original full coefficient restriction. -/
@[reassoc] theorem factorRatioInitialPolygonMap_coefficient (b : Bool) :
    F' b ≫ PolygonInfinitesimal.parameterProjection f τ τ' ht (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫ F b := by
  cases b <;> simp only [factorRatioInitialPolygonMap, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, Category.id_comp]
  · rw [PolygonInfinitesimal.chart_parameterProjection,
      ← polynomialFactorRatioChart_coefficient_assoc f W ha s τ hτ τ' hτ' ht
        b3 b4 b6 r hr I J hf hI hJ hrI h3]
  · rw [PolygonInfinitesimal.chart_parameterProjection, branchSwapIso_ringMap_assoc,
      ← polynomialFactorRatioChart_coefficient_assoc f W ha s τ hτ τ' hτ' ht
        b3 b4 b6 r hr I J hf hI hJ hrI h3]

end FLT.Mazur.WeierstrassDividedDepth
