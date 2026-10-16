/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceNodeMap
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeGeometry

/-!
# Distinct points of the full initial neighborhood with the same incidence

Over Q with a₁ = 1 and the other coefficients zero, the full neighborhood
is D(v+1). The points t=0, v=1 and t=0, v=-2 both belong to it. They have
identical (t,x)=(0,2), so retaining t as a node coordinate loses information.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.InitialIncidenceCollision
open WeierstrassModificationX

/-- A split nodal special fiber with unit linear tangent coefficient. -/
def curve : WeierstrassCurve ℚ := ⟨1, 0, 0, 0, 0⟩

local notation "A" => Coordinate curve 0 0 0 0
local notation "O" => PolynomialInitialOpen curve 0 0 0 0 (0 : ℚ[X])
local notation "D" => polynomialSmallFactor curve 0 0 0 0 (0 : ℚ[X]) +
  algebraMap ℚ A curve.a₁

/-- Every rational slope at incidence zero gives a point of this original special fiber. -/
def slopePoint (c : ℚ) : A →ₐ[ℚ] ℚ := evaluation curve 0 0 0 0 0 c (by simp)

@[simp] theorem slopePoint_t (c : ℚ) : slopePoint c (t curve 0 0 0 0) = 0 :=
  evaluation_t ..

@[simp] theorem slopePoint_v (c : ℚ) : slopePoint c (v curve 0 0 0 0) = c :=
  evaluation_v ..

/-- The deleted tangent divisor is evaluated without discarding any points. -/
theorem slopePoint_denominator (c : ℚ) : slopePoint c D = c + 1 := by
  simp only [map_add, polynomialSmallFactor, map_zero, slopePoint_v,
    sub_zero, AlgHom.commutes]
  rfl

/-- A slope different from -1 lies in the entire original initial node neighborhood. -/
def openSlopePoint (c : ℚ) (hc : c + 1 ≠ 0) : O →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom D (f := slopePoint c) (by
    rw [slopePoint_denominator]
    exact isUnit_iff_ne_zero.mpr hc)

/-- Evaluation on the open still evaluates all original functions. -/
theorem openSlopePoint_base (c : ℚ) (hc : c + 1 ≠ 0) (z : A) :
    openSlopePoint c hc (algebraMap A O z) = slopePoint c z := by
  rw [openSlopePoint, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The horizontal coordinate is quadratic on the original component t=0. -/
theorem slopePoint_x (c : ℚ) : slopePoint c (x curve 0 0 0 0) = c ^ 2 + c := by
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    slopePoint_v, slopePoint_t]
  norm_num [curve]

/-- The two indicated points on D(v+1) are distinct. -/
theorem openSlopePoint_one_ne_neg_two :
    openSlopePoint 1 (by norm_num) ≠ openSlopePoint (-2) (by norm_num) := by
  intro h
  have hv := congrArg (fun f : O →ₐ[ℚ] ℚ ↦ f (algebraMap A O (v curve 0 0 0 0))) h
  simp only [openSlopePoint_base, slopePoint_v] at hv
  norm_num at hv

/-- Nevertheless every incidence-node function has equal values at those two points. -/
theorem slopePoint_incidence_collision :
    (slopePoint 1).comp (incidenceNodeMap curve 0 0 0 0) =
      (slopePoint (-2)).comp (incidenceNodeMap curve 0 0 0 0) := by
  apply NodalFiber.hom_ext
  · simp only [AlgHom.comp_apply, incidenceNodeMap_p, slopePoint_t]
  · simp only [AlgHom.comp_apply, incidenceNodeMap_q, slopePoint_x]
    norm_num

end FLT.Mazur.InitialIncidenceCollision
