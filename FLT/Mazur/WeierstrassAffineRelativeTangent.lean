/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSingularJetTranslation
public import FLT.Mazur.RelativeJetSmoothObstruction
public import FLT.Mazur.WeierstrassAffineProduct

/-!
# Vertical tangent obstructions in the original affine chart

Every affine singular residue point of an arbitrary coefficient equation has
a relative tangent vector that cannot lift through the square-zero jet quotient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial PolygonNodePresentation WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (e : Coordinate W 2 →ₐ[R] K)
  (hy : 2 * e (coord W 2 1) + algebraMap R K W.a₁ * e (coord W 2 0) +
    algebraMap R K W.a₃ = 0)

/-- The original affine chart's vertical tangent vector at a residue point. -/
def affineRelativeTangent : Coordinate W 2 →ₐ[R] Jet K 2 :=
  evaluation W 2
    ![algebraMap K _ (e (coord W 2 0)),
      algebraMap K _ (e (coord W 2 1)) + jet 2 X, 1] (by
    apply (Projective.equation_some _ _).mpr
    have h := singularAffineJet_tangent_equation (W.map (algebraMap R K))
      (e (coord W 2 0)) (e (coord W 2 1)) (affine_equation_of_hom W e) hy
    simpa only [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R K (Jet K 2)]
      using h) rfl

/-- The tangent vector has the prescribed constant coordinates and vertical direction. -/
@[simp] theorem affineRelativeTangent_coord (i : Fin 3) :
    affineRelativeTangent W e hy (coord W 2 i) =
      ![algebraMap K _ (e (coord W 2 0)),
        algebraMap K _ (e (coord W 2 1)) + jet 2 X, 1] i := evaluation_coord _ _ _ _ _ i

/-- Truncating the tangent vector to its constant value recovers the original residue point. -/
theorem affineRelativeTangent_origin :
    ((jetEval (K := K)).restrictScalars R).comp (affineRelativeTangent W e hy) = e := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply, AlgHom.commutes]

/-- At a singular point, the relative tangent cannot lift to a third-order jet. -/
theorem affineRelativeTangent_no_lift
    (hx : algebraMap R K W.a₁ * e (coord W 2 1) -
      (3 * e (coord W 2 0) ^ 2 + 2 * algebraMap R K W.a₂ * e (coord W 2 0) +
        algebraMap R K W.a₄) = 0)
    (g : Coordinate W 2 →ₐ[R] Jet K 3) :
    ((jetDrop (K := K)).restrictScalars R).comp g ≠ affineRelativeTangent W e hy := by
  intro h
  have hxg : jetDrop (g (coord W 2 0)) = algebraMap K _ (e (coord W 2 0)) := by
    simpa using AlgHom.congr_fun h (coord W 2 0)
  have hyg : jetDrop (g (coord W 2 1)) =
      algebraMap K _ (e (coord W 2 1)) + jet 2 X := by
    simpa using AlgHom.congr_fun h (coord W 2 1)
  apply singularAffineJet_no_lift (W.map (algebraMap R K))
    (e (coord W 2 0)) (e (coord W 2 1)) hx hy _ _ hxg hyg
  simpa only [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R K (Jet K 3)]
    using affine_equation_of_hom W g

end FLT.Mazur.WeierstrassIntegralChart
