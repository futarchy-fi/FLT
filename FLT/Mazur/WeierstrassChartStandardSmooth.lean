/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartPresentation
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Standard smooth derivative localizations

Invert a partial derivative in a free coordinate of the actual cubic chart.
The composed presentation has four generators, three relations and unit
Jacobian, giving standard smoothness of relative dimension one. This local
construction does not require the discriminant to be a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j i : Fin 3) (hij : i ≠ j)

/-- The actual derivative localization with its explicitly invertible Jacobian. -/
def chartPartialSubmersive : Algebra.SubmersivePresentation R
    (Localization.Away (chartPartial W j i)) (Unit ⊕ Fin 3) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (Localization.Away (chartPartial W j i)) (chartPartial W j i)).comp
        (chartPreSubmersive W j i hij)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian,
      chartPreSubmersive_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (chartPartial W j i)).mul
      (IsLocalization.Away.algebraMap_isUnit (chartPartial W j i))

/-- Four variables and three relations give relative dimension one. -/
theorem chartPartialSubmersive_dimension : (chartPartialSubmersive W j i hij).dimension = 1 := by
  change Nat.card (Unit ⊕ Fin 3) - Nat.card (Unit ⊕ Fin 2) = 1
  norm_num [Nat.card_eq_fintype_card]

include hij

/-- Each free derivative localization is standard smooth of relative dimension one. -/
theorem chartPartial_standardSmooth_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Localization.Away (chartPartial W j i)) :=
  (chartPartialSubmersive W j i hij).isStandardSmoothOfRelativeDimension
    (chartPartialSubmersive_dimension W j i hij)

/-- In particular each derivative localization is a smooth algebra over the original base. -/
theorem chartPartial_smooth : Algebra.Smooth R (Localization.Away (chartPartial W j i)) := by
  let _ := (chartPartialSubmersive W j i hij).isStandardSmooth
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
