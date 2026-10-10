/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineVariableChangeMap

/-!
# Integral admissible changes give actual affine algebra isomorphisms

The concrete chart maps compose according to the variable-change group law.
Identity and inversion then give inverse algebra maps, without unfolding the
quotient-ring implementation of the original Weierstrass chart.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]

/-- The identity variable change is identity on the actual affine coordinate algebra. -/
theorem affineVariableChangeMap_one (W : WeierstrassCurve R) :
    affineVariableChangeMap W W 1 (one_smul _ _) = AlgHom.id R _ := by
  apply hom_ext
  intro i
  fin_cases i
  · change affineVariableChangeMap W W 1 _ (coord W 2 0) = coord W 2 0
    simp only [affineVariableChangeMap_x, VariableChange.one_def, Units.val_one,
      map_one, map_zero, one_pow, one_mul, add_zero]
  · change affineVariableChangeMap W W 1 _ (coord W 2 1) = coord W 2 1
    simp only [affineVariableChangeMap_y, VariableChange.one_def, Units.val_one,
      map_one, map_zero, one_pow, one_mul, zero_mul, add_zero]
  · change affineVariableChangeMap W W 1 _ (coord W 2 2) = coord W 2 2
    simp only [coord_self, map_one]

/-- Composition on original affine algebras agrees with admissible coordinate composition. -/
theorem affineVariableChangeMap_comp (W V U : WeierstrassCurve R) (C D : VariableChange R)
    (hD : D • W = V) (hC : C • V = U) (hCD : (C * D) • W = U) :
    (affineVariableChangeMap V U C hC).comp (affineVariableChangeMap W V D hD) =
      affineVariableChangeMap W U (C * D) hCD := by
  apply hom_ext
  intro i
  fin_cases i
  · change affineVariableChangeMap V U C hC
      (affineVariableChangeMap W V D hD (coord W 2 0)) =
        affineVariableChangeMap W U (C * D) hCD (coord W 2 0)
    simp only [affineVariableChangeMap_x, map_add, map_mul, map_pow,
      AlgHom.commutes, VariableChange.mul_def, Units.val_mul]
    ring
  · change affineVariableChangeMap V U C hC
      (affineVariableChangeMap W V D hD (coord W 2 1)) =
        affineVariableChangeMap W U (C * D) hCD (coord W 2 1)
    simp only [affineVariableChangeMap_x, affineVariableChangeMap_y,
      map_add, map_mul, map_pow, AlgHom.commutes, VariableChange.mul_def, Units.val_mul]
    ring
  · change affineVariableChangeMap V U C hC
      (affineVariableChangeMap W V D hD (coord W 2 2)) =
        affineVariableChangeMap W U (C * D) hCD (coord W 2 2)
    simp only [coord_self, map_one]

/-- The actual affine chart algebras are isomorphic under every integral variable change. -/
def affineVariableChangeEquiv (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) : Coordinate W 2 ≃ₐ[R] Coordinate V 2 := by
  have hi : C⁻¹ • V = W := by rw [← h, inv_smul_smul]
  refine AlgEquiv.ofAlgHom (affineVariableChangeMap W V C h)
    (affineVariableChangeMap V W C⁻¹ hi) ?_ ?_
  · have hc := affineVariableChangeMap_comp V W V C C⁻¹ hi h
      (by rw [mul_inv_cancel, one_smul])
    simpa only [mul_inv_cancel, affineVariableChangeMap_one] using hc
  · have hc := affineVariableChangeMap_comp W V W C⁻¹ C h hi
      (by rw [inv_mul_cancel, one_smul])
    simpa only [inv_mul_cancel, affineVariableChangeMap_one] using hc

/-- The isomorphism preserves the original coordinate formula for X. -/
theorem affineVariableChangeEquiv_x (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) :
    affineVariableChangeEquiv W V C h (coord W 2 0) =
      algebraMap R _ (C.u : R) ^ 2 * coord V 2 0 + algebraMap R _ C.r :=
  affineVariableChangeMap_x W V C h

/-- The isomorphism preserves the original coordinate formula for Y. -/
theorem affineVariableChangeEquiv_y (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) :
    affineVariableChangeEquiv W V C h (coord W 2 1) =
      algebraMap R _ (C.u : R) ^ 3 * coord V 2 1 +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * coord V 2 0 +
          algebraMap R _ C.t := affineVariableChangeMap_y W V C h

end FLT.Mazur.WeierstrassIntegralChart
