/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionSquare
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeRetraction

/-!
# The opposite original node comparison commutes between arithmetic orders

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

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

/-- The actual constructed arithmetic polygon comparisons commute with adjacent restriction. -/
@[reassoc] theorem arithmeticOppositeNodeChart_restriction_square :
    arithmeticPolygonNodeRestriction R π m ≫
      arithmeticOppositeNodeChart π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 =
    arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 ≫
      arithmeticSuccessiveRestriction R π m W s b3 b4 b6 := by
  unfold arithmeticOppositeNodeChart oppositePolygonChart simpleSlopePolygonChart
  rw [← Category.assoc, arithmeticIncidencePolygon_restriction_square]
  simp only [Category.assoc, arithmeticSuccessiveRestriction]
  congr 1
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (arithmeticOppositeNodeRetraction_restriction R π m W s b3 b4 b6 ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassSuccessiveX
