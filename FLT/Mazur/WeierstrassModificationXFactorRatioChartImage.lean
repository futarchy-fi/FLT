/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioGeometry

/-!
# Exact full factor-ratio chart image

The corrected initial chart is precisely D(y - 1) in its smoothing node,
including every nilpotent coefficient. Together with the full right
puncture this image covers the node over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "N" => NodalFiber.Coordinate τ
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "E" => polynomialFactorRatioIso W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "F" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The exact deleted tangent divisor in the normalized whole node. -/
theorem polynomialFactorRatioChart_range :
    Set.range F = (PrimeSpectrum.basicOpen (PolygonSmoothing.rightCoordinate τ - 1) :
      Set (PrimeSpectrum (PolygonSmoothing.ChartRing τ))) := by
  have hs : Function.Surjective (E).hom :=
    (Scheme.homeoOfIso E).surjective
  change Set.range (((NodalFiber.unitSmoothingIso τ τ 1 (by simp)).hom ∘
    PrimeSpectrum.comap (algebraMap N M)) ∘ (E).hom) = _
  rw [Set.range_comp, hs.range_eq, Set.image_univ, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range M (NodalFiber.q τ + algebraMap R N (-1 : R))]
  rw [← Scheme.coe_homeoOfIso, Homeomorph.image_eq_preimage_symm]
  ext x
  change (NodalFiber.unitSmoothingEquiv τ τ 1 (by simp)
    (NodalFiber.q τ + algebraMap R N (-1 : R)) ∉ x.asIdeal) ↔
      PolygonSmoothing.rightCoordinate τ - 1 ∉ x.asIdeal
  rw [map_add, NodalFiber.unitSmoothingEquiv_q, AlgEquiv.commutes, map_neg, map_one]
  simp only [sub_eq_add_neg]

/-- The full right puncture supplies all points omitted by the original initial chart. -/
theorem polynomialFactorRatioChart_right_cover (x : PolygonSmoothing.chart R τ) :
    x ∈ Set.range F ∨ x ∈ Set.range (PolygonSmoothing.rightBranchOpen R τ) := by
  rw [polynomialFactorRatioChart_range, PolygonSmoothing.rightBranchOpen_range]
  change PolygonSmoothing.rightCoordinate τ - 1 ∉ x.asIdeal ∨
    PolygonSmoothing.rightCoordinate τ ∉ x.asIdeal
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  have ha' := not_not.mp ha
  have hb' := not_not.mp hb
  have he : (1 : PolygonSmoothing.ChartRing τ) ∈ x.asIdeal := by
    convert x.asIdeal.sub_mem hb' ha' using 1
    ring
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal he isUnit_one)

end FLT.Mazur.WeierstrassModificationX
