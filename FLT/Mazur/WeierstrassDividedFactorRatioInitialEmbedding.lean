/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioInitialAffine
public import FLT.Mazur.WeierstrassDividedZeroMobiusInitialIntersection
public import FLT.Mazur.WeierstrassModificationXFactorRatioPuncturePreimage
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The whole original initial affine comparison is an open immersion

Exact puncture preimages show that cross-label equality in the polygon
comes from the original full overlap. This proves injectivity and then
open immersion at every nilpotent arithmetic order, with all corrections.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polynomialFactorRatioChart polynomialNodeChart
  polynomialOppositeNodeChart factorRatioInitialAffinePolygonMap
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "N" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "F" => factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3
local notation "a" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "b" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "C" => polynomialNodeOpenCover W s b3 b4 b6 r hr I hI hrI h3 ha
local notation "f" => factorRatioInitialAffinePolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3

/-- A cross-label equality lies in the actual original D(q), at every nilpotent order. -/
theorem factorRatioInitialPolygonMap_cross_preimage (x y : Spec (.of L))
    (h : F false x = F true y) : x ∈ Set.range (polynomialNodeOverlapInclusion W s) := by
  have hn : initialPolygonIndex k false ≠ initialPolygonIndex k true := by
    intro he
    have := initialPolygonIndex_injective k he
    contradiction
  have he := h
  simp only [factorRatioInitialPolygonMap, Bool.false_eq_true, ↓reduceIte,
    Category.id_comp] at he
  change PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega)
      (initialPolygonIndex k false) (N x) =
    PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega)
      (initialPolygonIndex k true) ((branchSwapIso R τ).hom (N y)) at he
  rcases (PolygonInfinitesimal.charts_eq_iff R τ (2 * k + 3) (by omega) hn _ _).mp he with
    ⟨z, hz, _, _⟩ | ⟨z, _, hx, _⟩
  · exact (initialPolygonIndex_not_reverse_preceding k hz).elim
  · rw [← polynomialFactorRatioChart_right_preimage W ha s τ hτ b3 b4 b6 r hr I hI hrI h3]
    exact ⟨(edgeInversion R).hom z, hx⟩

/-- No extra initial affine points are identified by the full corrected polygon comparison. -/
theorem factorRatioInitialPolygonMap_cross_eq (x y : Spec (.of L))
    (h : F false x = F true y) : a x = b y := by
  obtain ⟨z, rfl⟩ := factorRatioInitialPolygonMap_cross_preimage
    W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 x y h
  have he := congrArg (fun g ↦ g z)
    (factorRatioInitialPolygonMap_original_overlap τ k W ha s hτ b3 b4 b6 r hr I hI hrI h3)
  have hy := (F true).isOpenEmbedding.injective (he.symm.trans h)
  have hg := congrArg (fun g ↦ g z)
    (polynomialNodeOverlapOpposite_global W s b3 b4 b6 r hr I hI hrI h3)
  change b (polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 z) = _ at hg
  exact hg.symm.trans (congrArg b hy)

/-- The map from the entire original affine scheme is injective, not just its node restrictions. -/
theorem factorRatioInitialAffinePolygonMap_injective : Function.Injective f := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := (C).exists_eq x
  obtain ⟨j, y, rfl⟩ := (C).exists_eq y
  have he (i : Bool) (x : Spec (.of L)) : f ((C).f i x) = F i x :=
    congrArg (fun g ↦ g x)
      (factorRatioInitialAffinePolygonMap_chart W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 i)
  rw [he, he] at h
  cases i <;> cases j
  · exact congrArg a ((F false).isOpenEmbedding.injective h)
  · exact factorRatioInitialPolygonMap_cross_eq W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 x y h
  · exact (factorRatioInitialPolygonMap_cross_eq
      W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 y x h.symm).symm
  · exact congrArg b ((F true).isOpenEmbedding.injective h)

/-- The complete original affine comparison is an open immersion at every nilpotent order. -/
instance factorRatioInitialAffinePolygonMap_isOpenImmersion : IsOpenImmersion f := by
  apply IsOpenImmersion.of_openCover_source f C
    (factorRatioInitialAffinePolygonMap_injective W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3)
  intro i
  change Bool at i
  change IsOpenImmersion ((if i then b else a) ≫ f)
  rw [factorRatioInitialAffinePolygonMap_chart]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
