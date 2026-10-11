/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentChart
public import FLT.Mazur.WeierstrassOrdinaryDomainLift
public import FLT.Mazur.WeierstrassProjectiveChartProduct

/-!
# Constructed specializations at infinitesimal node points

Every square-zero node vector and every smooth affine slope give actual
algebra points of the cubic and of its original secant addition domain.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : R) (r q : Sˣ) (x y : S)
local notation "W" => WeierstrassCurve.mk a 0 0 0 0

/-- The smooth affine slope gives an actual normalized cubic point. -/
def splitNodalTangentParameterPoint (hq : (q : S) = (r : S) + algebraMap R S a) :
    Coordinate W 2 →ₐ[R] S :=
  evaluation W 2 ![(r : S) * q, (r : S) ^ 2 * q, 1] (by
    simp only [Projective.equation_iff, Projective.fin3_def_ext,
      WeierstrassCurve.map, toProjective, map_zero, mul_one, one_pow,
      zero_mul, add_zero]
    rw [hq]
    ring) rfl

/-- Every square-zero tangent vector is an actual point of the original nodal cubic. -/
def splitNodalTangentNodePoint
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    Coordinate W 2 →ₐ[R] S :=
  evaluation W 2 ![x, y, 1] (by
    simp only [Projective.equation_iff, Projective.fin3_def_ext,
      WeierstrassCurve.map, toProjective, map_zero, mul_one, one_pow,
      zero_mul, add_zero]
    linear_combination hyy + algebraMap R S a * hxy - x * hxx) rfl

/-- The parameter point retains exactly its original affine coordinates. -/
@[simp] theorem splitNodalTangentParameterPoint_coord
    (hq : (q : S) = (r : S) + algebraMap R S a) (i : Fin 3) :
    splitNodalTangentParameterPoint a r q hq (coord W 2 i) =
      ![(r : S) * q, (r : S) ^ 2 * q, 1] i := evaluation_coord _ _ _ _ _ i

/-- The node point retains the whole given tangent vector. -/
@[simp] theorem splitNodalTangentNodePoint_coord
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) (i : Fin 3) :
    splitNodalTangentNodePoint a x y hxx hxy hyy (coord W 2 i) = ![x, y, 1] i :=
  evaluation_coord _ _ _ _ _ i

variable (hq : (q : S) = (r : S) + algebraMap R S a)
  (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0)

/-- The actual pair of smooth affine and infinitesimal node points. -/
def splitNodalTangentPair : AffineProduct W →ₐ[R] S :=
  chartProductEvaluation W 2 2 (splitNodalTangentParameterPoint a r q hq)
    (splitNodalTangentNodePoint a x y hxx hxy hyy)

/-- The first projection of the pair is the constructed parameter point. -/
theorem splitNodalTangentPair_left (i : Fin 3) :
    splitNodalTangentPair a r q x y hq hxx hxy hyy (productLeft W (coord W 2 i)) =
      ![(r : S) * q, (r : S) ^ 2 * q, 1] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_left W 2 2
    (splitNodalTangentParameterPoint a r q hq)
    (splitNodalTangentNodePoint a x y hxx hxy hyy)) (coord W 2 i)
  exact h.trans (splitNodalTangentParameterPoint_coord a r q hq i)

/-- The second projection of the pair is the constructed node point. -/
theorem splitNodalTangentPair_right (i : Fin 3) :
    splitNodalTangentPair a r q x y hq hxx hxy hyy (productRight W (coord W 2 i)) =
      ![x, y, 1] i := by
  have h := DFunLike.congr_fun (chartProductEvaluation_right W 2 2
    (splitNodalTangentParameterPoint a r q hq)
    (splitNodalTangentNodePoint a x y hxx hxy hyy)) (coord W 2 i)
  exact h.trans (splitNodalTangentNodePoint_coord a x y hxx hxy hyy i)

/-- The genuine secant denominator is invertible at every constructed tangent pair. -/
theorem splitNodalTangentPair_denominator :
    IsUnit (splitNodalTangentPair a r q x y hq hxx hxy hyy (secantDenominator W)) := by
  simpa only [secantDenominator, map_sub, productX₁, productX₂,
    splitNodalTangentPair_left, splitNodalTangentPair_right, Matrix.cons_val_zero] using
    splitNodalTangent_denominator_isUnit r q x hxx

/-- Every tangent pair factors through the actual original secant addition domain. -/
def splitNodalTangentLift : additionChartRing W (ordinaryIndex false) →ₐ[R] S :=
  ordinaryDomainLift W false (splitNodalTangentPair a r q x y hq hxx hxy hyy)
    (splitNodalTangentPair_denominator a r q x y hq hxx hxy hyy)

/-- The constructed secant lift retains exactly both prescribed input points. -/
theorem splitNodalTangentLift_restriction :
    (splitNodalTangentLift a r q x y hq hxx hxy hyy).comp
        (additionChartAlgRestriction W (ordinaryIndex false)) =
      splitNodalTangentPair a r q x y hq hxx hxy hyy :=
  ordinaryDomainLift_restriction W false _ _

end FLT.Mazur.WeierstrassIntegralChart
