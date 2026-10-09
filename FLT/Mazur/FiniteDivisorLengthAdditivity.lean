/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTwistedDegree
public import FLT.Mazur.DivisorLineBundleSum

/-!
# Additivity of actual finite Cartier divisor length

The divisor tensor comparison and the cohomological degree formula prove that
multiplying finite Cartier ideals adds their scheme lengths. Intersections and
repeated components are allowed; no disjointness or reducedness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I J : X.IdealSheafData} (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
  [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)]
  [IsFinite ((I * J).subschemeι ≫ f)]

include hI hJ in
/-- The actual closed scheme length adds under Cartier ideal multiplication. -/
theorem divisorFieldLength_mul :
    divisorFieldLength f (I * J) = divisorFieldLength f I + divisorFieldLength f J := by
  have h := curveSheafDegree_iso f (divisorLineBundleSumIso hI hJ)
  rw [divisor_degree_eq_fieldLength f (hI.mul hJ),
    curveSheafDegree_divisor_tensor f hI hJ.divisorLineBundle_locallyFreeRankOne,
    divisor_degree_eq_fieldLength f hJ] at h
  omega

end FLT.Mazur.FCurve
