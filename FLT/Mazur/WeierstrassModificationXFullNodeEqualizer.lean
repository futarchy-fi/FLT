/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOrigin
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.NodeLocalizedEqualizer

/-!
# The actual first attachment node as a localized equalizer

Normalize the original denominator by its nonzero origin value. The resulting
localization retains both original factors, including the opposite tangent.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonNodeEqualizer PolygonNodePresentation
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (a c : K) (ha : IsUnit a)
local notation "N" => NodalFiber.Coordinate (0 : K)
local notation "A" => PolygonNodeEqualizer.A (R := K)

/-- The original denominator in the polynomial-pair node algebra. -/
def fullNodePairDenominator : A := NodalFiber.polygonNodeEquiv (fullNodeDenominator a c)

/-- The denominator scaled to value one at the origin. -/
def fullNodeNormalizedDenominator : A :=
  algebraMap K A a⁻¹ * fullNodePairDenominator a c

/-- The original denominator evaluates to the nonzero tangent coefficient. -/
theorem fullNodePairDenominator_value : aEval (fullNodePairDenominator a c) = a := by
  simp [fullNodePairDenominator, fullNodeDenominator, aEval]

include ha in
/-- Normalization leaves a saturated principal neighborhood of the origin. -/
theorem fullNodeNormalizedDenominator_value :
    aEval (fullNodeNormalizedDenominator a c) = 1 := by
  rw [fullNodeNormalizedDenominator, map_mul, AlgHom.commutes,
    fullNodePairDenominator_value, Algebra.algebraMap_self, RingHom.id_apply,
    inv_mul_cancel₀ ha.ne_zero]

include ha in
/-- Normalization changes the denominator only by a unit. -/
theorem fullNodeDenominator_associated :
    Associated (fullNodeNormalizedDenominator a c) (fullNodePairDenominator a c) :=
  associated_unit_mul_left _ _ ((ha.inv).map (algebraMap K A))

/-- The actual attachment localization as pairs of localized functions with equal origin. -/
abbrev FullNodeEqualizer := NodeLocalizedEqualizer.E (fullNodeNormalizedDenominator a c)
  (fullNodeNormalizedDenominator_value a c ha)

instance fullNodeEqualizer_isLocalization :
    IsLocalization.Away (fullNodePairDenominator a c) (FullNodeEqualizer a c ha) :=
  IsLocalization.Away.of_associated (fullNodeDenominator_associated a c ha)

/-- The original localization is exactly the localized two-branch equalizer. -/
def fullNodeEqualizerEquiv : FullNodeOpen a c ≃+* FullNodeEqualizer a c ha :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (fullNodeDenominator a c))
    (T := Submonoid.powers (fullNodePairDenominator a c))
    _ _ NodalFiber.polygonNodeEquiv.toRingEquiv
    (by rw [Submonoid.map_powers]; rfl)

/-- The comparison preserves every original product-zero function. -/
theorem fullNodeEqualizerEquiv_base (x : N) :
    fullNodeEqualizerEquiv a c ha (algebraMap N (FullNodeOpen a c) x) =
      NodeLocalizedEqualizer.restriction (fullNodeNormalizedDenominator a c)
        (fullNodeNormalizedDenominator_value a c ha) (NodalFiber.polygonNodeEquiv x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

include ha in
/-- On the first branch the denominator retains the conic parameter factor. -/
theorem fullNodeNormalizedDenominator_first :
    first (fullNodeNormalizedDenominator a c) = 1 - C c * X ^ 2 := by
  simp only [fullNodeNormalizedDenominator, fullNodePairDenominator, fullNodeDenominator,
    map_mul, map_add, map_sub, map_one, map_pow, AlgEquiv.commutes,
    NodalFiber.polygonNodeEquiv_p, NodalFiber.polygonNodeEquiv_q, AlgHom.commutes,
    PolygonNodeLocalization.first_x, PolygonNodeLocalization.first_y, zero_add]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha.ne_zero, map_one, one_mul]
  rfl

/-- On the second branch the opposite tangent remains inverted even when c vanishes. -/
theorem fullNodeNormalizedDenominator_second :
    second (fullNodeNormalizedDenominator a c) = C a⁻¹ * (X + C a) := by
  simp [fullNodeNormalizedDenominator, fullNodePairDenominator, fullNodeDenominator]

end FLT.Mazur.WeierstrassModificationX
