/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioChartNaturality
public import FLT.Mazur.WeierstrassDividedInitialPolygonBoundary

/-!
# Corrected full initial nodes at their original cyclic polygon labels

The corrected smoothing and both original labels are retained. The opposite
label uses the same full corrected chart followed by the original branch swap.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "C" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- Both complete corrected initial nodes occupy their original cyclic labels. -/
def factorRatioInitialPolygonMap (b : Bool) : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  C ≫ (if b then (branchSwapIso R τ).hom else 𝟙 _) ≫
    PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k b)
local notation "F" => factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3

instance factorRatioInitialPolygonMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold factorRatioInitialPolygonMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Both full corrected labeled charts preserve the original coefficient structure. -/
@[reassoc] theorem factorRatioInitialPolygonMap_base (b : Bool) :
    F b ≫ PolygonInfinitesimal.toBase R τ (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W s))) := by
  cases b <;> simp only [factorRatioInitialPolygonMap, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, PolygonInfinitesimal.chart_toBase, retainedPolygonSwap_base, Category.id_comp]
  all_goals exact polynomialFactorRatioChart_structure W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

end FLT.Mazur.WeierstrassDividedDepth
