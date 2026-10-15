/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXOppositeNodeGeometry
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNode
public import FLT.Mazur.WeierstrassModificationXCoefficients
public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart

/-!
# Both full initial nodes cover at every arithmetic order

The opposite comparison and joint scheme coverage specialize to the original
coefficient-extended equation over every R/(π^(m+1)).
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)

/-- The opposite original arithmetic neighborhood has an explicit full node inverse. -/
def arithmeticOppositeInitialNodeEquiv :
    PolynomialOppositeInitialOpen (W.map q) (q s) (q b3) (q b4) (q b6) r₀ ≃ₐ[Q]
      PolynomialNodeOpen (W.map q) (q s) :=
  polynomialOppositeNodeEquiv (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The opposite full node chart in the unchanged original arithmetic equation. -/
def arithmeticOppositeInitialNodeChart : Spec (.of (PolynomialNodeOpen (W.map q) (q s))) ⟶
    Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q)) :=
  polynomialOppositeNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The opposite comparison is an actual open immersion at every quotient order. -/
theorem arithmeticOppositeInitialNodeChart_isOpenImmersion :
    IsOpenImmersion (arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) :=
  polynomialOppositeNodeChart_isOpenImmersion ..

/-- The opposite arithmetic node comparison preserves the original coefficient morphism. -/
@[reassoc] theorem arithmeticOppositeInitialNodeChart_structure :
    arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q (ExtendedCoordinate W s b3 b4 b6 Q))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap Q (PolynomialNodeOpen (W.map q) (q s)))) :=
  polynomialOppositeNodeChart_structure ..

/-- The two full original initial nodes cover the entire arithmetic scheme at every order. -/
theorem arithmeticInitialNodeCharts_cover
    (p : Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q))) :
    p ∈ Set.range (arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ∨
      p ∈ Set.range (arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) :=
  polynomialNodeCharts_cover (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)
    (ha.map q) p

end FLT.Mazur.WeierstrassModificationX
