/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlap
public import FLT.Mazur.WeierstrassModificationXNodeIncidenceOpen
public import FLT.Mazur.WeierstrassModificationXOverlapRatioReflection

/-!
# The full tangent ratio on the actual original node intersection

Both original tangent factors are units on PolynomialNodeOverlap. Their ratio
therefore defines an actual Laurent parameter there, and original reflection
sends it to its reciprocal, including every arithmetic correction.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r

/-- All original initial functions on the full standard overlap. -/
def polynomialNodeOverlapEvaluation : A →ₐ[R] O :=
  (Algebra.algHom R L O).comp
    (polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3)

local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3

/-- The original small tangent factor is the actual localized second node coordinate. -/
theorem polynomialNodeOverlapEvaluation_small :
    G V = algebraMap L O (algebraMap N L (NodalFiber.q s)) := by
  change algebraMap L O
    (polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 _ _ _ _ V) = _
  rw [polynomialNodeEvaluation_small]

/-- The overlap inverts precisely the small tangent factor as well. -/
theorem polynomialNodeOverlap_small_isUnit : IsUnit (G V) := by
  rw [polynomialNodeOverlapEvaluation_small]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The opposite factor was already a unit on the entire first initial neighborhood. -/
theorem polynomialNodeOverlap_opposite_isUnit : IsUnit (G U) :=
  (polynomialNodeForwardBase_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3).map
    (algebraMap L O)

/-- The full tangent-ratio parameter on the actual initial-node intersection. -/
def polynomialNodeOverlapRatio : Oˣ :=
  initialOverlapRatioUnit W s b3 b4 b6 r G
    (polynomialNodeOverlap_small_isUnit W s b3 b4 b6 r hr I hI hrI h3)
    (polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3)

/-- The original initial reflection inverts the actual full-overlap Laurent parameter. -/
theorem polynomialNodeOverlapRatio_reflection :
    initialOverlapRatioUnit W s b3 b4 b6 r
      ((G).comp ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom)
      (initialOverlap_reflected_small_isUnit W s b3 b4 b6 r G
        (polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3))
      (initialOverlap_reflected_opposite_isUnit W s b3 b4 b6 r G
        (polynomialNodeOverlap_small_isUnit W s b3 b4 b6 r hr I hI hrI h3)) =
          (polynomialNodeOverlapRatio W s b3 b4 b6 r hr I hI hrI h3)⁻¹ :=
  initialOverlapRatioUnit_reflection W s b3 b4 b6 r G _ _

/-- This evaluation is the actual composite into the original initial affine chart. -/
@[reassoc] theorem polynomialNodeOverlapEvaluation_spec :
    polynomialNodeOverlapInclusion W s ≫
      polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
        Spec.map (CommRingCat.ofHom (G).toRingHom) := by
  rw [polynomialNodeOverlapInclusion, polynomialNodeChart_eq_spec, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
