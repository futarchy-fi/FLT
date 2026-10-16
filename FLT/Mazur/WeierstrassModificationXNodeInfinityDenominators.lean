/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapDenominator

/-!
# The original infinity open is the full initial-node intersection

The original y function cuts out exactly the intersection of both full node
neighborhoods over nilpotent bases. All polynomial corrections are retained.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "f" => algebraMap R[X] A
local notation "a" => algebraMap R A W.a₁
local notation "v₀" => v W s b3 b4 b6
local notation "t₀" => t W s b3 b4 b6
local notation "u" => polynomialSmallFactor W s b3 b4 b6 r
local notation "w" => polynomialOppositeFactor W s b3 b4 b6 r
local notation "D" => polynomialOppositeDenominator W s b3 b4 b6 r

include hr hI hrI h3 in
/-- The original y vanishes at a prime precisely when at least one node denominator does. -/
theorem polynomialInitialY_mem_iff (z : PrimeSpectrum A) :
    y W s b3 b4 b6 ∈ z.asIdeal ↔ (u + a ∈ z.asIdeal ∨ D ∈ z.asIdeal) := by
  have hrz : f r ∈ z.asIdeal :=
    (nilpotent_iff_mem_prime.mp ((NilpotentQuadraticRoot.element_nilpotent (I.map C)
      (polynomialArithmeticIdeal_nilpotent I hI) hrI).map f)) z.asIdeal z.isPrime
  have hbz : algebraMap R A b3 ∈ z.asIdeal :=
    (nilpotent_iff_mem_prime.mp ((NilpotentQuadraticRoot.element_nilpotent I hI h3).map
      (algebraMap R A))) z.asIdeal z.isPrime
  have hcz : f r + algebraMap R A b3 * t₀ ∈ z.asIdeal :=
    z.asIdeal.add_mem hrz (z.asIdeal.mul_mem_right _ hbz)
  have hl : f (polynomialSlopeLinear W b3) = a + algebraMap R A b3 * t₀ := by
    have hc (c : R) : f (C c) = algebraMap R A c :=
      (IsScalarTower.algebraMap_apply R R[X] A c).symm
    simp only [polynomialSlopeLinear, map_add, map_mul, t, hc]
  have hu : u ∈ z.asIdeal ↔ v₀ ∈ z.asIdeal := z.asIdeal.sub_mem_iff_left hrz
  have hw : w ∈ z.asIdeal ↔ v₀ + a ∈ z.asIdeal := by
    have he : w = (v₀ + a) + (f r + algebraMap R A b3 * t₀) := by
      rw [polynomialOppositeFactor, map_add, hl]
      ring
    rw [he]
    exact z.asIdeal.add_mem_iff_left hcz
  have hf : u + a ∈ z.asIdeal ↔ v₀ + a ∈ z.asIdeal := by
    have he : u + a = (v₀ + a) - f r := by rw [polynomialSmallFactor]; ring
    rw [he]
    exact z.asIdeal.sub_mem_iff_left hrz
  have hd : D ∈ z.asIdeal ↔ v₀ ∈ z.asIdeal := by
    have he : D = -v₀ - (f r + algebraMap R A b3 * t₀) := by
      rw [polynomialOppositeDenominator, polynomialOppositeFactor, map_add, hl]
      ring
    rw [he, z.asIdeal.sub_mem_iff_left hcz, z.asIdeal.neg_mem_iff]
  rw [y, polynomialFactors_horizontal W s b3 b4 b6 r hr]
  simp only [z.isPrime.mul_mem_iff_mem_or_mem, hu, hw, hf, hd]
  tauto

/-- The complete original infinity localization is the intersection of the two node images. -/
theorem polynomialInitialY_node_intersection :
    (PrimeSpectrum.basicOpen (y W s b3 b4 b6) : Set (PrimeSpectrum A)) =
      Set.range (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) ∩
        Set.range (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) := by
  rw [polynomialNodeChart_range, polynomialOppositeNodeChart_range]
  ext z
  change (y W s b3 b4 b6 ∉ z.asIdeal) ↔ (u + a ∉ z.asIdeal ∧ D ∉ z.asIdeal)
  rw [polynomialInitialY_mem_iff W s b3 b4 b6 r hr I hI hrI h3]
  exact not_or

/-- On the first full node the original infinity open is the full standard D(q). -/
theorem polynomialNodeChart_infinity_preimage :
    (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) ⁻¹'
      (PrimeSpectrum.basicOpen (y W s b3 b4 b6) : Set (PrimeSpectrum A)) =
        (PrimeSpectrum.basicOpen (algebraMap (NodalFiber.Coordinate s)
          (PolynomialNodeOpen W s) (NodalFiber.q s)) :
            Set (PrimeSpectrum (PolynomialNodeOpen W s))) := by
  rw [polynomialInitialY_node_intersection W s b3 b4 b6 r hr I hI hrI h3,
    Set.preimage_inter, Set.preimage_range, Set.univ_inter,
    polynomialNodeChart_opposite_preimage]

end FLT.Mazur.WeierstrassModificationX
