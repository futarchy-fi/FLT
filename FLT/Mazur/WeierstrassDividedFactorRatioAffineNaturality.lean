/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioPolygonNaturality
public import FLT.Mazur.WeierstrassDividedFactorRatioInitialAffine
public import FLT.Mazur.WeierstrassModificationXOppositeNodeCoefficientNaturality

/-!
# The glued full affine polygon map preserves original coefficients

The two original full node charts detect the coefficient square after gluing.
Every nilpotent correction and the complete normalized smoothing are retained.
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
local notation "A" => factorRatioInitialAffinePolygonMap W ha s τ hτ k
  b3 b4 b6 r hr I hI hrI h3
local notation "A'" => factorRatioInitialAffinePolygonMap U (ha.map f) (f s) τ' hτ' k
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)
local notation "C'" => polynomialNodeOpenCover U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3) (ha.map f)
local notation "N'" => polynomialNodeChart U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)
local notation "O'" => polynomialOppositeNodeChart U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)
local notation "p" => PolygonInfinitesimal.parameterProjection f τ τ' ht (2 * k + 3) (by omega)
local notation "g" => Spec.map (CommRingCat.ofHom (coefficientRingMap f W s b3 b4 b6))

/-- The glued complete initial affine map follows the original full coefficient restriction. -/
@[reassoc] theorem factorRatioInitialAffinePolygonMap_coefficient :
    A' ≫ p = g ≫ A := by
  apply (C').hom_ext
  intro b
  change Bool at b
  change (if b then O' else N') ≫ (A' ≫ p) = (if b then O' else N') ≫ (g ≫ A)
  rw [← Category.assoc, factorRatioInitialAffinePolygonMap_chart,
    factorRatioInitialPolygonMap_coefficient f W ha s τ hτ τ' hτ' ht
      k b3 b4 b6 r hr I J hf hI hJ hrI h3]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← polynomialNodeChart_coefficient_assoc f W s b3 b4 b6 r hr I J hf hI hJ hrI h3]
    exact congrArg (fun z ↦ Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫ z)
      (factorRatioInitialAffinePolygonMap_chart W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 false).symm
  · simp only [↓reduceIte]
    rw [← polynomialOppositeNodeChart_coefficient_assoc
      f W s b3 b4 b6 r hr I J hf hI hJ hrI h3]
    exact congrArg (fun z ↦ Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫ z)
      (factorRatioInitialAffinePolygonMap_chart W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 true).symm

end FLT.Mazur.WeierstrassDividedDepth
