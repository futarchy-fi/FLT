/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassTriangularCoordinates

/-!
# A full cubic comparison determines its admissible change uniquely

The coefficients of 1, x and y recover r, t, u², u³ and u²s from the actual
coordinate map. The unit u is then recovered without dividing by 2 or 3.
-/

@[expose] public noncomputable section
open WeierstrassCurve CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C D : VariableChange R) (hC : C • W = V) (hD : D • W = V)

/-- The actual affine algebra map determines every admissible change coordinate. -/
theorem affineVariableChangeMap_faithful
    (h : affineVariableChangeMap W V C hC = affineVariableChangeMap W V D hD) : C = D := by
  have hx := DFunLike.congr_fun h (coord W 2 0)
  have hy := DFunLike.congr_fun h (coord W 2 1)
  rw [affineVariableChangeMap_x, affineVariableChangeMap_x] at hx
  rw [affineVariableChangeMap_y, affineVariableChangeMap_y] at hy
  have hx' : algebraMap R _ C.r + algebraMap R _ ((C.u : R) ^ 2) * coord V 2 0 +
      algebraMap R _ 0 * coord V 2 1 =
      algebraMap R _ D.r + algebraMap R _ ((D.u : R) ^ 2) * coord V 2 0 +
        algebraMap R _ 0 * coord V 2 1 := by
    simp only [map_zero, zero_mul, add_zero, map_pow]
    linear_combination hx
  obtain ⟨hr, hu2, _⟩ := lowCoordinate_injective V hx'
  have hy' : algebraMap R _ C.t + algebraMap R _ ((C.u : R) ^ 2 * C.s) * coord V 2 0 +
      algebraMap R _ ((C.u : R) ^ 3) * coord V 2 1 =
      algebraMap R _ D.t + algebraMap R _ ((D.u : R) ^ 2 * D.s) * coord V 2 0 +
        algebraMap R _ ((D.u : R) ^ 3) * coord V 2 1 := by
    simp only [map_pow, map_mul]
    linear_combination hy
  obtain ⟨ht, hs, hu3⟩ := lowCoordinate_injective V hy'
  have hu : C.u = D.u := by
    apply Units.ext
    apply (C.u.isUnit.pow 2).mul_left_cancel
    calc
      (C.u : R) ^ 2 * (C.u : R) = (C.u : R) ^ 3 := (pow_succ _ 2).symm
      _ = (D.u : R) ^ 3 := hu3
      _ = (C.u : R) ^ 2 * (D.u : R) := by rw [pow_succ, hu2]
  rw [← hu] at hs
  exact VariableChange.ext hu hr ((C.u.isUnit.pow 2).mul_left_cancel hs) ht

/-- Equality of the whole proper cubic maps recovers the original affine algebra map. -/
theorem integralVariableChangeIso_affine_faithful
    (h : integralVariableChangeIso W V C hC = integralVariableChangeIso W V D hD) :
    affineVariableChangeMap W V C hC = affineVariableChangeMap W V D hD := by
  have he := congrArg (fun e : integralCurve V ≅ integralCurve W ↦
    integralCurveChart V 2 ≫ e.hom) h
  rw [integralVariableChangeIso_affine, integralVariableChangeIso_affine] at he
  have he' := (cancel_mono (integralCurveChart W 2)).mp he
  apply AlgHom.coe_ringHom_injective
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he')

/-- An actual full curve comparison has at most one admissible coordinate change. -/
theorem integralVariableChangeIso_faithful
    (h : integralVariableChangeIso W V C hC = integralVariableChangeIso W V D hD) : C = D :=
  affineVariableChangeMap_faithful W V C D hC hD
    (integralVariableChangeIso_affine_faithful W V C D hC hD h)

end FLT.Mazur.WeierstrassIntegralChart
