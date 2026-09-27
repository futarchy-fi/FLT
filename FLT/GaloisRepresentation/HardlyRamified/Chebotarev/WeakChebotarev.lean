/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.DegreeOneGenerator
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FiniteMonoidCover
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.GeneratorDensity

/-!
# The weak Chebotarev theorem for finite monoid quotients

Discharges the explicit W1 and W2 hypotheses of the W2 and W3 leaves, giving
`PowerFrobCover` unconditionally.
-/

@[expose] public section

namespace GaloisRepresentation.Chebotarev

universe u v

/-- W1 as a proposition, discharged by `logDensity_generators`. -/
theorem w1Statement : W1Statement.{u, v} :=
  fun K L _ _ _ _ _ _ _ => logDensity_generators K L

/-- W2 as used by W3, discharged by `exists_degreeOne_generator`. -/
theorem w2Statement : W2Statement.{0} := by
  intro L _ _ _ g S N
  exact exists_degreeOne_generator L g w1Statement S N

end GaloisRepresentation.Chebotarev

namespace GaloisRepresentation.B5Inputs

open GaloisRepresentation.Chebotarev

/-- W3: every element of a finite discrete monoid image of the absolute Galois
group of `ℚ` is a conjugate of a nonnegative power of a chosen rational
Frobenius, outside any finite set and above any bound. -/
theorem powerFrobCover_of_finite
    {M : Type*} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (Prime ℚ)) (N : ℕ) : PowerFrobCover f S N :=
  powerFrobCover w2Statement f S N

end GaloisRepresentation.B5Inputs
