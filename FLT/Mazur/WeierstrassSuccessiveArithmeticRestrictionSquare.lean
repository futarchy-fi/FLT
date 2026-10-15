/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticRetractionRestriction

/-!
# The original node comparison commutes between arithmetic orders

The constructed polygon node open at order m is the restriction of the open
at order m+1. Both arrows use the actual original quotient restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))

/-- The polygon tensor restriction retains the original incidence presentation. -/
@[reassoc] theorem arithmeticIncidencePolygon_restriction_square :
    arithmeticPolygonNodeRestriction R π m ≫
      Spec.map (CommRingCat.ofHom (SuccessiveIncidence.toPolygon (q₁ π)).toRingHom) =
    Spec.map (CommRingCat.ofHom (SuccessiveIncidence.toPolygon (q₀ π)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (SuccessiveIncidence.coefficientRingMap f (q₁ π))) := by
  let _ := (f).toAlgebra
  exact SuccessiveIncidence.toPolygon_restriction_square Q₁ Q₀ (q₁ π)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

/-- The actual constructed arithmetic polygon comparisons commute with adjacent restriction. -/
@[reassoc] theorem arithmeticNodeChart_restriction_square :
    arithmeticPolygonNodeRestriction R π m ≫
      arithmeticNodeChart π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 =
    arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 ≫
      arithmeticSuccessiveRestriction R π m W s b3 b4 b6 := by
  unfold arithmeticNodeChart nilpotentPolygonChart
  rw [← Category.assoc, arithmeticIncidencePolygon_restriction_square]
  simp only [Category.assoc, nilpotentNodeChart, arithmeticSuccessiveRestriction]
  congr 1
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (arithmeticNodeRetraction_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassSuccessiveX
