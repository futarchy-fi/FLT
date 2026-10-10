/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionSlopeFamilies

/-!
# Coordinate formulas for the two families of addition outputs

The ordinary maps have affine coordinates. The reciprocal maps have the
same homogeneous formula, multiplied by their invertible normalizing factor.
These formulas commute with arbitrary algebra specializations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The ordinary output map with a uniform affine codomain. -/
def ordinaryChartAddition (b : Bool) : Coordinate W 2 →ₐ[R]
    additionChartRing W (ordinaryIndex b) :=
  match b with
  | false => secantAddition W
  | true => tangentAddition W

/-- The reciprocal output map with a uniform infinity-chart codomain. -/
def reciprocalChartAddition (b : Bool) : Coordinate W 1 →ₐ[R]
    additionChartRing W (reciprocalIndex b) :=
  match b with
  | false => verticalSecantAddition W
  | true => verticalTangentAddition W

/-- The normalizing inverse for the reciprocal output. -/
def reciprocalChartInverse (b : Bool) : additionChartRing W (reciprocalIndex b) :=
  match b with
  | false => reciprocalTargetInverse W _ (verticalSecantSlope W)
  | true => reciprocalTargetInverse W _ (verticalTangentSlope W)

/-- The reciprocal normalization factor is a unit. -/
theorem reciprocalChartInverse_isUnit (b : Bool) : IsUnit (reciprocalChartInverse W b) := by
  cases b <;> exact Units.isUnit _

/-- Ordinary output coordinates are the classical affine addition coordinates. -/
theorem ordinaryChartAddition_coord (b : Bool) (i : Fin 3) :
    ordinaryChartAddition W b (coord W 2 i) =
      ![(W.map (algebraMap R (additionChartRing W (ordinaryIndex b)))).toAffine.addX
          (additionChartAlgRestriction W (ordinaryIndex b) (productX₁ W))
          (additionChartAlgRestriction W (ordinaryIndex b) (productX₂ W))
          (ordinaryChartSlope W b),
        (W.map (algebraMap R (additionChartRing W (ordinaryIndex b)))).toAffine.addY
          (additionChartAlgRestriction W (ordinaryIndex b) (productX₁ W))
          (additionChartAlgRestriction W (ordinaryIndex b) (productX₂ W))
          (additionChartAlgRestriction W (ordinaryIndex b) (productY₁ W))
          (ordinaryChartSlope W b), 1] i := by
  cases b
  · exact secantAddition_coord W i
  · exact tangentAddition_coord W i

/-- Reciprocal output coordinates retain the polynomial formula after normalization. -/
theorem reciprocalChartAddition_coord (b : Bool) (i : Fin 3) :
    reciprocalChartAddition W b (coord W 1 i) =
      reciprocalChartInverse W b *
        reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
          (reciprocalChartSlope W b) i := by
  cases b
  · change verticalSecantAddition W (coord W 1 i) = _
    rw [verticalSecantAddition, reciprocalAddition_coord, reciprocalCoordinates_map]
    rfl
  · change verticalTangentAddition W (coord W 1 i) = _
    rw [verticalTangentAddition, reciprocalAddition_coord, reciprocalCoordinates_map]
    rfl

/-- The ordinary coordinate formula commutes with an arbitrary algebra map. -/
theorem ordinaryChartAddition_map_coord (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S) (i : Fin 3) :
    f (ordinaryChartAddition W b (coord W 2 i)) =
      ![(W.map (algebraMap R S)).toAffine.addX
          (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₁ W)))
          (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₂ W)))
          (f (ordinaryChartSlope W b)),
        (W.map (algebraMap R S)).toAffine.addY
          (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₁ W)))
          (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₂ W)))
          (f (additionChartAlgRestriction W (ordinaryIndex b) (productY₁ W)))
          (f (ordinaryChartSlope W b)), 1] i := by
  rw [ordinaryChartAddition_coord]
  fin_cases i <;>
    simp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, AlgHom.commutes]

end FLT.Mazur.WeierstrassIntegralChart
