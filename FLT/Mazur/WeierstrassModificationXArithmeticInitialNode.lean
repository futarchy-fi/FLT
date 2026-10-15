/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeGeometry
public import FLT.Mazur.WeierstrassModificationXCoefficients
public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart

/-!
# Constructed full initial node charts at every arithmetic order

The original initial coefficients construct both inverse coordinate maps over
R/(π^(m+1)). The comparison includes the complement of the incidence open.
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

/-- The actual full original initial arithmetic neighborhood has a constructed node inverse. -/
def arithmeticInitialNodeEquiv :
    PolynomialInitialOpen (W.map q) (q s) (q b3) (q b4) (q b6) r₀ ≃ₐ[Q]
      PolynomialNodeOpen (W.map q) (q s) :=
  polynomialNodeEquiv (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The constructed full node chart in the original arithmetic initial equation. -/
def arithmeticInitialNodeChart : Spec (.of (PolynomialNodeOpen (W.map q) (q s))) ⟶
    Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q)) :=
  polynomialNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The full arithmetic comparison is an actual open immersion at every quotient order. -/
theorem arithmeticInitialNodeChart_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) :=
  polynomialNodeChart_isOpenImmersion ..

/-- The full initial node chart preserves the actual original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialNodeChart_structure :
    arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q (ExtendedCoordinate W s b3 b4 b6 Q))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap Q (PolynomialNodeOpen (W.map q) (q s)))) :=
  polynomialNodeChart_structure ..

end FLT.Mazur.WeierstrassModificationX
