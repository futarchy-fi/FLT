/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomLocusFppfCoverage
public import FLT.Mazur.OddWeierstrassCyclicHomLocusFppfCoverage

/-!
# The two actual characteristic charts for cyclic subgroups

Both charts carry their scheme-theoretic universal orbit subgroup. The odd
chart retains characteristic two; the even chart retains characteristic three.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
variable (n : ℕ) [NeZero n]

/-- The original two closed subgroup loci, indexed by the odd auxiliary choice. -/
def locus : Bool → Scheme
  | false => UniversalWeierstrass.cyclicHomUniversalMultiplicationLocus n
  | true => OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocus n

/-- The entire generalized curve on each actual characteristic chart. -/
def curve : (b : Bool) → GeneralizedEllipticCurve (locus n b)
  | false => UniversalWeierstrass.cyclicHomSourceCurve n
      (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n)
  | true => OddWeierstrassParameter.cyclicHomSourceCurve n
      (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n)

/-- Each chart carries the full universal subgroup, including non-etale fibers. -/
def subgroup : (b : Bool) → (curve n b).FiniteSubgroup n
  | false => UniversalWeierstrass.cyclicHomUniversalSubgroup n
  | true => OddWeierstrassParameter.cyclicHomUniversalSubgroup n

end FLT.Mazur.CyclicCharacteristicAtlas
