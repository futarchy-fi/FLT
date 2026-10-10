/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineVariableChangeEquiv
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# Actual affine scheme isomorphisms and their marked sections

The integral algebra isomorphism gives an isomorphism of original affine
charts over the base. The original coordinate formulas detect its effect
on actual scheme sections, retaining the bridge needed for marked descent.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The actual coefficient-preserving affine scheme isomorphism of a variable change. -/
def affineVariableChangeIso : chartScheme V 2 ≅ chartScheme W 2 :=
  Scheme.Spec.mapIso (affineVariableChangeEquiv W V C h).toRingEquiv.toCommRingCatIso.op

/-- The affine scheme isomorphism preserves the original structure morphism. -/
theorem affineVariableChangeIso_base :
    (affineVariableChangeIso W V C h).hom ≫ chartStructure W 2 = chartStructure V 2 :=
  specAlgHom_structure (affineVariableChangeMap W V C h)

/-- The original transformation formulas determine equality of actual section evaluations. -/
theorem affineVariableChange_evaluation (p : Coordinate V 2 →ₐ[R] R)
    (q : Coordinate W 2 →ₐ[R] R)
    (hx : (C.u : R) ^ 2 * p (coord V 2 0) + C.r = q (coord W 2 0))
    (hy : (C.u : R) ^ 3 * p (coord V 2 1) + (C.u : R) ^ 2 * C.s * p (coord V 2 0) +
      C.t = q (coord W 2 1)) :
    p.comp (affineVariableChangeMap W V C h) = q := by
  apply hom_ext
  intro i
  fin_cases i
  · change p (affineVariableChangeMap W V C h (coord W 2 0)) = q (coord W 2 0)
    simpa only [affineVariableChangeMap_x, map_add, map_mul, map_pow,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hx
  · change p (affineVariableChangeMap W V C h (coord W 2 1)) = q (coord W 2 1)
    simpa only [affineVariableChangeMap_y, map_add, map_mul, map_pow,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hy
  · change p (affineVariableChangeMap W V C h (coord W 2 2)) = q (coord W 2 2)
    simp only [coord_self, map_one]

/-- Matching coordinates proves equality of entire original ring-valued scheme sections. -/
theorem affineVariableChangeIso_section (p : Coordinate V 2 →ₐ[R] R)
    (q : Coordinate W 2 →ₐ[R] R)
    (hx : (C.u : R) ^ 2 * p (coord V 2 0) + C.r = q (coord W 2 0))
    (hy : (C.u : R) ^ 3 * p (coord V 2 1) + (C.u : R) ^ 2 * C.s * p (coord V 2 0) +
      C.t = q (coord W 2 1)) :
    Spec.map (CommRingCat.ofHom p.toRingHom) ≫ (affineVariableChangeIso W V C h).hom =
      Spec.map (CommRingCat.ofHom q.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (affineVariableChange_evaluation W V C h p q hx hy)

/-- Original coordinate values determine the coordinates on the changed chart uniquely. -/
theorem affineVariableChange_evaluation_coordinates (p : Coordinate V 2 →ₐ[R] R)
    (q : Coordinate W 2 →ₐ[R] R) (he : p.comp (affineVariableChangeMap W V C h) = q)
    (x y : R) (hx : (C.u : R) ^ 2 * x + C.r = q (coord W 2 0))
    (hy : (C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t = q (coord W 2 1)) :
    p (coord V 2 0) = x ∧ p (coord V 2 1) = y := by
  have ex := DFunLike.congr_fun he (coord W 2 0)
  have ey := DFunLike.congr_fun he (coord W 2 1)
  simp only [AlgHom.comp_apply, affineVariableChangeMap_x, map_add, map_mul, map_pow,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at ex
  simp only [AlgHom.comp_apply, affineVariableChangeMap_y, map_add, map_mul, map_pow,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at ey
  have hpx : p (coord V 2 0) = x := by
    apply sub_eq_zero.mp
    apply (C.u.isUnit.pow 2).mul_right_eq_zero.mp
    linear_combination ex - hx
  refine ⟨hpx, ?_⟩
  apply sub_eq_zero.mp
  apply (C.u.isUnit.pow 3).mul_right_eq_zero.mp
  rw [hpx] at ey
  linear_combination ey - hy

end FLT.Mazur.WeierstrassIntegralChart
