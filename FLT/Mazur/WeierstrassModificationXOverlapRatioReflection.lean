/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInvolution

/-!
# Exact reciprocal tangent ratios under the original reflection

Where both full tangent factors are units, their ratio is a unit. The
original reflection sends this ratio to its inverse, including all polynomial
and nilpotent corrections. No residue reduction is used.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r
variable (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hv : IsUnit (g (polynomialSmallFactor W s b3 b4 b6 r)))
  (hu : IsUnit (g (polynomialOppositeFactor W s b3 b4 b6 r)))

/-- The full tangent ratio on the original two-neighborhood intersection. -/
def initialOverlapRatioUnit : Sˣ := hv.unit * hu.unit⁻¹

/-- The actual value retains both complete tangent factors. -/
theorem initialOverlapRatioUnit_coe :
    (initialOverlapRatioUnit W s b3 b4 b6 r g hv hu : S) = g V * ↑hu.unit⁻¹ := by
  simp only [initialOverlapRatioUnit, Units.val_mul, IsUnit.unit_spec]

local notation "g'" => AlgHom.comp g
  (AlgEquiv.toAlgHom (AlgEquiv.restrictScalars R (initialReflection W s b3 b4 b6)))

include hu in
/-- The reflected small factor is a unit because it is the negative opposite factor. -/
theorem initialOverlap_reflected_small_isUnit : IsUnit (g' V) := by
  change IsUnit (g (initialReflection W s b3 b4 b6 V))
  rw [initialReflection_small, map_neg]
  exact hu.neg

include hv in
/-- The reflected opposite factor is a unit because it is the negative small factor. -/
theorem initialOverlap_reflected_opposite_isUnit : IsUnit (g' U) := by
  change IsUnit (g (initialReflection W s b3 b4 b6 U))
  rw [initialReflection_opposite, map_neg]
  exact hv.neg

/-- Reflection turns the original full overlap ratio into its exact reciprocal. -/
theorem initialOverlapRatioUnit_reflection :
    initialOverlapRatioUnit W s b3 b4 b6 r g'
      (initialOverlap_reflected_small_isUnit W s b3 b4 b6 r g hu)
      (initialOverlap_reflected_opposite_isUnit W s b3 b4 b6 r g hv) =
        (initialOverlapRatioUnit W s b3 b4 b6 r g hv hu)⁻¹ := by
  have hs : g' V = -g U := by
    change g (initialReflection W s b3 b4 b6 V) = _
    rw [initialReflection_small, map_neg]
  have ho : g' U = -g V := by
    change g (initialReflection W s b3 b4 b6 U) = _
    rw [initialReflection_opposite, map_neg]
  have hs' : (initialOverlap_reflected_small_isUnit W s b3 b4 b6 r g hu).unit =
      -hu.unit := by
    apply Units.ext
    simpa only [IsUnit.unit_spec, Units.val_neg] using hs
  have ho' : (initialOverlap_reflected_opposite_isUnit W s b3 b4 b6 r g hv).unit =
      -hv.unit := by
    apply Units.ext
    simpa only [IsUnit.unit_spec, Units.val_neg] using ho
  simp only [initialOverlapRatioUnit, hs', ho', inv_neg, neg_mul_neg, mul_inv_rev, inv_inv]

end FLT.Mazur.WeierstrassModificationX
