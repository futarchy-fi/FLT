/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# Coefficient extension preserves the original infinity section

The normalized infinity coordinates commute with every coefficient map.
Consequently the actual global zero section is natural over arbitrary bases.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

local notation "V" => W.map (algebraMap R S)

/-- Infinity evaluation commutes with the actual normalized coefficient map. -/
theorem chartCoefficientMap_infinity :
    ((chartInfinityEvaluation (S := S) V).restrictScalars R).comp
        (chartCoefficientMap W 1) =
      (Algebra.ofId R S).comp (chartInfinityEvaluation (S := R) W) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
      chartInfinityEvaluation_coord, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fin.reduceFinMk, Matrix.head_cons, Matrix.tail_cons, map_zero, map_one]

/-- The global coefficient morphism preserves the actual zero section. -/
@[reassoc] theorem integralCoefficientMorphism_zero :
    integralCurveZero V ≫ integralCoefficientMorphism W =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W := by
  rw [integralCurveZero, Category.assoc, integralCurveChart_coefficientMorphism,
    integralCurveZero, ← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ integralCurveChart W 1)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (chartCoefficientMap_infinity (S := S) W)

end FLT.Mazur.WeierstrassIntegralChart
