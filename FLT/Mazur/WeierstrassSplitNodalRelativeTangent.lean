/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalObstruction
public import FLT.Mazur.RelativeJetSmoothObstruction

/-!
# Residue-field tangent vectors for the relative split nodal cubic

The vertical tangent vector and its obstruction are defined over any
coefficient ring mapping to the residue field, without a field base assumption.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (a : Rˣ)

/-- The original affine cubic relation over an arbitrary coefficient ring. -/
theorem splitNodalRelativeAffine_relation :
    coord (splitNodalEquation a) 2 1 ^ 2 +
      algebraMap R _ a * coord (splitNodalEquation a) 2 0 *
        coord (splitNodalEquation a) 2 1 - coord (splitNodalEquation a) 2 0 ^ 3 = 0 := by
  have h := coord_equation (splitNodalEquation a) 2
  rw [WeierstrassCurve.Projective.equation_iff] at h
  dsimp [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective] at h ⊢
  simpa only [coord_self, map_zero, zero_mul, add_zero, mul_one, one_pow] using h

/-- The relative vertical tangent vector, with values in residue-field jets. -/
def splitNodalRelativeTangent : Coordinate (splitNodalEquation a) 2 →ₐ[R] Jet K 2 :=
  evaluation _ 2 ![0, jet 2 X, 1] (by
    rw [WeierstrassCurve.Projective.equation_iff]
    change jet (K := K) 2 X ^ 2 * 1 + algebraMap R _ a * 0 * jet 2 X * 1 +
      algebraMap R _ 0 * jet 2 X * 1 ^ 2 -
      (0 ^ 3 + algebraMap R _ 0 * 0 ^ 2 * 1 +
        algebraMap R _ 0 * 0 * 1 ^ 2 + algebraMap R _ 0 * 1 ^ 3) = 0
    simp only [map_zero, mul_zero, zero_mul, zero_pow (by omega : 3 ≠ 0),
      add_zero, mul_one, sub_zero]
    rw [← map_pow, ← map_zero (jet 2), jet_eq_iff]
    intro d hd
    simp [coeff_X_pow, show d ≠ 2 by omega]) rfl

@[simp] theorem splitNodalRelativeTangent_coord (i : Fin 3) :
    splitNodalRelativeTangent (K := K) a (coord (splitNodalEquation a) 2 i) =
      ![0, jet 2 X, 1] i := evaluation_coord _ _ _ _ _ i

/-- The relative vertical tangent cannot lift through the square-zero truncation. -/
theorem splitNodalRelativeTangent_no_lift
    (g : Coordinate (splitNodalEquation a) 2 →ₐ[R] Jet K 3) :
    ((jetDrop (K := K)).restrictScalars R).comp g ≠ splitNodalRelativeTangent a := by
  intro h
  have hx : jetDrop (g (coord (splitNodalEquation a) 2 0)) = 0 := by
    simpa using AlgHom.congr_fun h (coord (splitNodalEquation a) 2 0)
  have hy : jetDrop (g (coord (splitNodalEquation a) 2 1)) = jet 2 X := by
    simpa using AlgHom.congr_fun h (coord (splitNodalEquation a) 2 1)
  apply splitNodalJet_obstruction (algebraMap R K a) _ _ hx hy
  simpa only [map_sub, map_add, map_pow, map_mul, AlgHom.commutes, map_zero,
    ← IsScalarTower.algebraMap_apply R K (Jet K 3)] using
    congrArg g (splitNodalRelativeAffine_relation a)

end FLT.Mazur.WeierstrassIntegralChart
