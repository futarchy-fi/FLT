/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlap
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorNodes

/-!
# Full initial-node intersections on the original arithmetic tensor scheme

The complete standard D(q) meets both actual tensor node charts. The comparison
retains all original functions and holds at every quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
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


local notation "P" => polynomialNodeOverlapInclusion (W.map q) (q s)
local notation "F" => arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "G" => arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6

/-- The entire standard D(q) restricted to the actual opposite arithmetic node. -/
def arithmeticNodeOverlapOpposite :=
  polynomialNodeOverlapOpposite (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
    (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)

/-- The full initial tensor nodes intersect exactly in the complete standard D(q). -/
theorem arithmeticTensorNodes_isPullback :
    IsPullback P (arithmeticNodeOverlapOpposite π m W s b3 b4 b6 ha h2 h3 h4 h6) F G := by
  have H := polynomialNodeOverlap_isPullback (W.map q) (q s) (q b3) (q b4) (q b6)
    r₀ hr₀ J (arithmeticParameterIdeal_nilpotent π m) hm₀
      (arithmeticCoefficient_mem π m h3)
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (arithmeticInitialTensorIso π m W s b3 b4 b6).hom H.cone H.isLimit)

/-- The two standard intersection legs agree on every function of the original tensor chart. -/
@[reassoc] theorem arithmeticTensorNodes_overlap :
    P ≫ F = arithmeticNodeOverlapOpposite π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫ G :=
  (arithmeticTensorNodes_isPullback π m W s b3 b4 b6 ha h2 h3 h4 h6).w

/-- The complete standard puncture is the actual tensor-node fiber product. -/
def arithmeticTensorNodesPullbackIso :=
  (arithmeticTensorNodes_isPullback π m W s b3 b4 b6 ha h2 h3 h4 h6).isoPullback

end FLT.Mazur.WeierstrassModificationX
