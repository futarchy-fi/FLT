/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeOrigin
public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.NodeLocalizedEqualizer

/-!
# The full middle attachment as a localized equalizer for arbitrary conic constant

The original denominator 1-c*z² has value one at the origin. Localizing the
polynomial-pair node therefore keeps the original conic parameter open and
an entire horizontal affine line, including when c is nonzero.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonNodeEqualizer PolygonNodePresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] (c : K)
local notation "B" => SuccessiveIncidence.Coordinate (0 : K)
local notation "A" => PolygonNodeEqualizer.A (R := K)

/-- The exact original attachment denominator in the polynomial-pair node. -/
def middleNodePairDenominator : A := NodalFiber.polygonNodeEquiv (middleNodeDenominator c)

/-- The unchanged denominator in the original ordered node coordinates. -/
theorem middleNodePairDenominator_eq : middleNodePairDenominator c =
    1 - algebraMap K A c * PolygonNodeLocalization.x ^ 2 := by
  have hc : NodalFiber.polygonNodeEquiv (algebraMap K B c) = algebraMap K A c :=
    NodalFiber.polygonNodeEquiv.commutes c
  have hz : NodalFiber.polygonNodeEquiv (SuccessiveIncidence.t (0 : K)) =
      PolygonNodeLocalization.x := NodalFiber.polygonNodeEquiv_p
  rw [middleNodePairDenominator, middleNodeDenominator, map_sub, map_one, map_mul,
    map_pow, hc, hz]

/-- The original middle denominator needs no rescaling at the origin. -/
theorem middleNodePairDenominator_value : aEval (middleNodePairDenominator c) = 1 := by
  simp [middleNodePairDenominator_eq, aEval]

/-- Pairs of localized branch functions with the same original origin value. -/
abbrev MiddleNodeEqualizer := NodeLocalizedEqualizer.E (middleNodePairDenominator c)
  (middleNodePairDenominator_value c)

/-- The original full localized node ring is precisely the actual branch equalizer. -/
def middleNodeEqualizerEquiv : MiddleNodeOpen c ≃+* MiddleNodeEqualizer c :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (middleNodeDenominator c))
    (T := Submonoid.powers (middleNodePairDenominator c))
    _ _ NodalFiber.polygonNodeEquiv.toRingEquiv
    (by rw [Submonoid.map_powers]; rfl)

/-- Every function of the original product-zero node is retained by the comparison. -/
theorem middleNodeEqualizerEquiv_base (x : B) :
    middleNodeEqualizerEquiv c (algebraMap B (MiddleNodeOpen c) x) =
      NodeLocalizedEqualizer.restriction (middleNodePairDenominator c)
        (middleNodePairDenominator_value c) (NodalFiber.polygonNodeEquiv x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

/-- The first branch retains the complete original conic parameter denominator. -/
theorem middleNodePairDenominator_first :
    first (middleNodePairDenominator c) = 1 - C c * X ^ 2 := by
  simp [middleNodePairDenominator_eq]

/-- The horizontal branch is the whole affine line, with no extra puncture. -/
theorem middleNodePairDenominator_second : second (middleNodePairDenominator c) = 1 := by
  simp [middleNodePairDenominator_eq]

end FLT.Mazur.WeierstrassSuccessiveX
