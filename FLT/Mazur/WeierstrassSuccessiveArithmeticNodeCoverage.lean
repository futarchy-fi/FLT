/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeNodeChart
public import FLT.Mazur.WeierstrassSuccessiveOppositeNodeChart

public import FLT.Mazur.WeierstrassSuccessiveNodeChartCoverage

/-!
# Coverage of the original arithmetic successive chart

At every quotient order the two constructed polygon maps cover the original
three-coordinate spectrum. This is the local cover used in the global atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

/-- The actual arithmetic polygon maps cover the entire original successive chart. -/
theorem arithmeticNodeCharts_cover (p : Spec (.of (ExtendedCoordinate W s π b3 b4 b6 Q))) :
    (∃ x, arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 x = p) ∨
      ∃ x, arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 x = p :=
  nilpotentPolygonCharts_cover (W.map q) (q s) (q π) (q b3) (q b4) (q b6)
    (ideal Q (parameter R π m)) (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) p

/-- The image union is the whole spectrum, for the specified arithmetic quotient. -/
theorem arithmeticNodeCharts_range_union :
    Set.range (arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6) ∪
      Set.range (arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  exact arithmeticNodeCharts_cover π m W s b3 b4 b6 ha hs h2 h3 h4 h6

end FLT.Mazur.WeierstrassSuccessiveX
