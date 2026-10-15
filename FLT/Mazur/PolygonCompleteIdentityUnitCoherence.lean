/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityMulCoherence
public import FLT.Mazur.PolygonCompleteIdentityFiniteReduction

/-!
# Original coefficient laws and their errors commute with finite restriction

Full faithfulness transfers the proved geometric compatibility to the actual
coefficient algebra maps. Their units and additive errors thus form compatible
systems in the original double Laurent algebras.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "r" => AlgHom.toRingHom (restriction K m)
local notation "f" j => AlgHom.toRingHom (completeIdentityFiniteMulAlgebra K n h i j)

/-- The actual original coefficient algebra laws commute with adjacent coefficient restriction. -/
theorem completeIdentityFiniteMulAlgebra_restriction :
    (coeffMap (coeffMap (r))).comp (f (m + 1)) =
      (f m).comp (coeffMap (r)) := by
  have he := completeIdentityFiniteMulCoordinates_restriction K n h i m
  rw [← completeIdentityFiniteMulAlgebra_spec,
    ← completeIdentityFiniteMulAlgebra_spec] at he
  rw [← Spec.map_comp, ← Spec.map_comp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The actual original multiplication units form a compatible finite system. -/
theorem completeIdentityFiniteMulUnit_restriction :
    Units.map (coeffMap (coeffMap (r))).toMonoidHom
        (completeIdentityFiniteMulUnit K n h i (m + 1)) =
      completeIdentityFiniteMulUnit K n h i m := by
  apply Units.ext
  change coeffMap (coeffMap (r)) ((f (m + 1)) (LaurentPolynomial.T 1)) =
    (f m) (LaurentPolynomial.T 1)
  have he := congrArg (fun g : (Ring K (m + 1))[T;T⁻¹] →+*
      (Ring K m)[T;T⁻¹][T;T⁻¹] ↦ g (LaurentPolynomial.T 1))
    (completeIdentityFiniteMulAlgebra_restriction K n h i m)
  simpa only [RingHom.comp_apply, coeffMap_T_one] using he

/-- The remaining full multiplication error is compatible with the actual finite restrictions. -/
theorem completeIdentityFiniteMulDefect_restriction :
    coeffMap (coeffMap (r)) (completeIdentityFiniteMulDefect K n h i (m + 1)) =
      completeIdentityFiniteMulDefect K n h i m := by
  have he := congrArg Units.val (completeIdentityFiniteMulUnit_restriction K n h i m)
  change coeffMap (coeffMap (r)) _ = _ at he
  rw [completeIdentityFiniteMulDefect, map_sub, he, completeIdentityFiniteMulDefect]
  simp only [map_mul, coeffMap_C, coeffMap_T_one]

end FLT.Mazur.PolygonInfinitesimalStages
