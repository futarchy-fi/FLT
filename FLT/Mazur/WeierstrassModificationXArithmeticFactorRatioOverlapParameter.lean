/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapFactorRatioBoundary
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialFactorRatio
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeOverlap

/-!
# Exact arithmetic parameters on both full initial overlap legs

The canonical polynomial root supplies one Laurent parameter on the original
D(q). Both whole-node restrictions retain that parameter, with inversion on
the opposite leg, before any accumulated node transport.
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


local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "N" => arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6

/-- The full original arithmetic D(q) carries its unreduced factor-ratio parameter. -/
def arithmeticFactorRatioOverlapParameter :
    Spec (.of (PolynomialNodeOverlap (W.map q) (q s))) ⟶ PolygonSmoothing.branchTorus Q :=
  factorRatioOverlapParameter (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

local notation "P" => arithmeticFactorRatioOverlapParameter π m W s b3 b4 b6 ha h2 h3 h4 h6

/-- The entire first overlap leg has the canonical full arithmetic boundary. -/
@[reassoc] theorem arithmeticInitialFactorRatioChart_overlap_first :
    polynomialNodeOverlapInclusion (W.map q) (q s) ≫ N =
      P ≫ PolygonSmoothing.rightBranchOpen Q τ := by
  exact polynomialFactorRatioChart_overlap_first (W.map q) (ha.map q) (q s) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s))
    (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The actual opposite overlap leg retains exactly the reciprocal full parameter. -/
@[reassoc] theorem arithmeticInitialFactorRatioChart_overlap_opposite :
    arithmeticNodeOverlapOpposite π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫ N =
      P ≫ (PolygonSmoothing.edgeInversion Q).hom ≫
        PolygonSmoothing.rightBranchOpen Q τ := by
  exact polynomialFactorRatioChart_overlap_opposite (W.map q) (ha.map q) (q s) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s))
    (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

end FLT.Mazur.WeierstrassModificationX
