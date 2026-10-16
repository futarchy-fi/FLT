/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapOppositeEvaluation

/-!
# Original coordinates of the full opposite-node restriction

The actual geometric restriction sends q to minus the entire opposite
factor and p to minus t times the small factor. These identities hold
before any arithmetic reduction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3

/-- Every original affine function transforms by its actual reflection on the opposite leg. -/
theorem polynomialNodeOverlapOppositeEvaluation_reflection (z : A) :
    H (E z) = G (initialReflection W s b3 b4 b6 z) := by
  have h := polynomialNodeOverlapOppositeEvaluation_global W s b3 b4 b6 r hr I hI hrI h3
    (initialReflection W s b3 b4 b6 z)
  have hi : initialReflection W s b3 b4 b6 (initialReflection W s b3 b4 b6 z) = z :=
    (initialReflection W s b3 b4 b6).symm_apply_apply z
  rw [hi] at h
  exact h

/-- The original first node coordinate becomes the negative opposite corrected incidence. -/
theorem polynomialNodeOverlapOppositeEvaluation_p :
    H (algebraMap N L (NodalFiber.p s)) =
      -(G (t W s b3 b4 b6) * G (polynomialSmallFactor W s b3 b4 b6 r)) := by
  have hp : E (t W s b3 b4 b6 * polynomialOppositeFactor W s b3 b4 b6 r) =
      algebraMap N L (NodalFiber.p s) := polynomialNodeEvaluation_first ..
  rw [← hp, polynomialNodeOverlapOppositeEvaluation_reflection, map_mul,
    initialReflection_t, initialReflection_opposite, map_mul, map_neg]
  exact mul_neg (G (t W s b3 b4 b6)) (G (polynomialSmallFactor W s b3 b4 b6 r))

/-- The original second node coordinate becomes minus the complete opposite tangent factor. -/
theorem polynomialNodeOverlapOppositeEvaluation_q :
    H (algebraMap N L (NodalFiber.q s)) =
      -G (polynomialOppositeFactor W s b3 b4 b6 r) := by
  have hq : E (polynomialSmallFactor W s b3 b4 b6 r) =
      algebraMap N L (NodalFiber.q s) := polynomialNodeEvaluation_small ..
  calc
    H (algebraMap N L (NodalFiber.q s)) = H (E (polynomialSmallFactor W s b3 b4 b6 r)) :=
      congrArg H hq.symm
    _ = _ := by rw [polynomialNodeOverlapOppositeEvaluation_reflection,
      initialReflection_small, map_neg]

end FLT.Mazur.WeierstrassModificationX
