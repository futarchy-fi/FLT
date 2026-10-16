/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroMobiusOverlapBoundary

/-!
# The entire polygon opposite puncture pulls back to the original overlap

The denominator of q/(q+a₁) is a unit on the full initial node. Thus its
nonvanishing locus is precisely D(q), including over a nonreduced base ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
local notation "L" => PolynomialNodeOpen W 0

/-- The fractional coordinate vanishes at exactly the primes containing the original q. -/
theorem zeroInitialFraction_mem_iff (z : PrimeSpectrum L) :
    NodalFiber.zeroTangentFraction W.a₁ ∈ z.asIdeal ↔
      NodalFiber.zeroTangentQ W.a₁ ∈ z.asIdeal := by
  unfold NodalFiber.zeroTangentFraction
  exact z.asIdeal.mul_unit_mem_iff_mem (Units.isUnit _)

/-- The full opposite polygon puncture pulls back to the entire original standard overlap. -/
theorem zeroInitialMobiusChart_right_preimage :
    (zeroInitialMobiusChart W ha) ⁻¹' Set.range (PolygonSmoothing.rightBranchOpen R 0) =
      Set.range (polynomialNodeOverlapInclusion W 0) := by
  rw [PolygonSmoothing.rightBranchOpen_range, polynomialNodeOverlapInclusion_range,
    zeroInitialMobiusChart, NodalFiber.zeroTangentMobiusChart_eq_spec]
  ext z
  change (NodalFiber.zeroTangentMobiusEvaluation (zeroInitialTangentUnit W ha)
    (PolygonSmoothing.rightCoordinate 0) ∉ z.asIdeal) ↔
      NodalFiber.zeroTangentQ W.a₁ ∉ z.asIdeal
  rw [NodalFiber.zeroTangentMobiusEvaluation_right]
  exact not_congr (zeroInitialFraction_mem_iff W z)

end FLT.Mazur.WeierstrassModificationX
