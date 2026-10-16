/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeForwardCoefficientNaturality

/-!
# Full original node factors follow arithmetic coefficient change

Both evaluated factors retain the original polynomial root and the corrected
incidence parameter. These identities apply before any zero-fiber restriction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "F₀" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "F₁" => polynomialNodeForwardBase U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s

/-- The entire opposite factor, including its incidence corrections, follows coefficient change. -/
theorem polynomialNodeForwardBase_opposite_coefficient :
    g (F₀ (polynomialOppositeFactor W s b3 b4 b6 r)) =
      F₁ (polynomialOppositeFactor U (f s) (f b3) (f b4) (f b6) (r.map f)) := by
  dsimp only [polynomialNodeForwardBase]
  rw [polynomialNodeEvaluation_opposite, polynomialNodeEvaluation_opposite]
  simp only [map_add, map_mul, nodeOpenCoefficientRingMap_q,
    nodeOpenCoefficientRingMap_scalar, nodeOpenCoefficientRingMap_eval,
    WeierstrassCurve.map_a₁]
  rw [polynomialNodeInverseT_coefficient f W s b3 r I J hf hI hJ hrI h3]

/-- The complete small factor follows the original coefficient restriction as well. -/
theorem polynomialNodeForwardBase_small_coefficient :
    g (F₀ (polynomialSmallFactor W s b3 b4 b6 r)) =
      F₁ (polynomialSmallFactor U (f s) (f b3) (f b4) (f b6) (r.map f)) := by
  dsimp only [polynomialNodeForwardBase]
  rw [polynomialNodeEvaluation_small, polynomialNodeEvaluation_small]
  exact nodeOpenCoefficientRingMap_q f W s

end FLT.Mazur.WeierstrassModificationX
