/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart
public import FLT.Mazur.WeierstrassSuccessiveOppositeNodeChart

/-!
# The opposite original node chart at every arithmetic order

Divisibility of the original non-tangent coefficients by π constructs the opposite node
open in the original successive equation over R/(π^(m+1)). The coefficient
ring need not contain its residue field, and no comparison is an input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The opposite polygon node chart in the original arithmetic successive equation. -/
def arithmeticOppositeNodeChart : Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
    Spec (.of (ExtendedCoordinate W s π b3 b4 b6 Q)) :=
  oppositePolygonChart (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

/-- Every opposite arithmetic node comparison is an actual open immersion. -/
theorem arithmeticOppositeNodeChart_isOpenImmersion :
    IsOpenImmersion (arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6) :=
  oppositePolygonChart_isOpenImmersion ..

/-- The opposite arithmetic open preserves the original quotient coefficients. -/
@[reassoc] theorem arithmeticOppositeNodeChart_structure :
    arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q (ExtendedCoordinate W s π b3 b4 b6 Q))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) :=
  oppositePolygonChart_structure ..

end FLT.Mazur.WeierstrassSuccessiveX
