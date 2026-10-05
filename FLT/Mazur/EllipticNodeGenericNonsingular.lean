/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel
public import FLT.Mazur.EllipticNodeDiscriminantDepth

/-!
# Generic nonsingularity of a finite-depth split node

Exact finite depth of a₆ and the deep coefficient conditions force a nonzero
discriminant. Every integral solution therefore gives a genuine generic
point, even when its reduction is the singular node.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ}

/-- The exact coefficient depth forces the discriminant to be nonzero. -/
theorem SplitNodeDepth.discriminant_ne_zero (D : SplitNodeDepth W π n) : W.Δ ≠ 0 := by
  intro h
  apply D.a₆_not_mem
  apply (node_discriminant_mem_pow_iff W D.a₁_unit D.a₂_mem
    (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem) (n + 1)
    D.a₃_mem D.a₄_mem).mp
  rw [h]
  exact Ideal.zero_mem _

/-- Every integral solution of a finite-depth split model is generically nonsingular. -/
theorem SplitNodeDepth.generic_nonsingular {K : Type*} [Field K] {A : ValuationSubring K}
    {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    {x y : A} (he : W.toAffine.Equation x y) :
    (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K) := by
  apply ((W.map (algebraMap A K)).toAffine.equation_iff_nonsingular_of_Δ_ne_zero ?_).mp
  · exact he.map (algebraMap A K)
  · rw [WeierstrassCurve.map_Δ]
    exact fun h => D.discriminant_ne_zero ((IsFractionRing.injective A K) (by simpa using h))

end FLT.Mazur
