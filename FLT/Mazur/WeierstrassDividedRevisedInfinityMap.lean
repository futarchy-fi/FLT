/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedAffineMaps

/-!
# The entire original arithmetic infinity chart in the revised polygon

The complete regular infinity factor ratio agrees with the whole affine
comparison through the original projective transition at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "b3" => Data.b3 d₀
local notation "b4" => Data.b4 d₀
local notation "b6" => Data.b6 d₀
local notation "J" => ideal Q (parameter R π m)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (H.a1_unit.map q)
  (arithmeticCoefficient_mem π m H.a2_div) (arithmeticCoefficient_mem π m (H.b3_div _))
  (arithmeticCoefficient_mem π m (H.b4_div _)) (arithmeticCoefficient_mem π m (H.b6_div _))
local notation "hr" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (H.a1_unit.map q)
  (arithmeticCoefficient_mem π m H.a2_div) (arithmeticCoefficient_mem π m (H.b3_div _))
  (arithmeticCoefficient_mem π m (H.b4_div _)) (arithmeticCoefficient_mem π m (H.b6_div _))
local notation "hm" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (H.a1_unit.map q)
  (arithmeticCoefficient_mem π m H.a2_div) (arithmeticCoefficient_mem π m (H.b3_div _))
  (arithmeticCoefficient_mem π m (H.b4_div _)) (arithmeticCoefficient_mem π m (H.b6_div _))
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu
local notation "hc" => arithmeticRevisedPolygon_initial_initial data H m j hj u hu

/-- The full original specialized infinity cubic maps into the revised initial edge. -/
def arithmeticOriginalRevisedInfinityMap :
    Spec (.of (WeierstrassIntegralChart.Coordinate (W.map q) 1)) ⟶
      arithmeticRevisedPolygon data H m j hj u hu :=
  factorRatioInfinityTargetMap (W.map q) (q (π ^ 1)) τ (q b3) r J
    (arithmeticParameterIdeal_nilpotent π m) hm
    (arithmeticCoefficient_mem π m (H.b3_div _)) c
    (arithmeticCoefficient_mem π m H.a2_div)
    (arithmeticCoefficient_mem π m (H.a3_div data))
    (arithmeticCoefficient_mem π m (H.a4_div data))
    (arithmeticCoefficient_mem π m (H.a6_div data))

/-- The actual full projective transition agrees in the independent target. -/
@[reassoc] theorem arithmeticOriginalRevisedInfinityMap_initial :
    Spec.map (CommRingCat.ofHom
      (arithmeticFactorRatioInfinityTransition π m W (π ^ 1) b3 b4 b6
        (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)).toRingHom) ≫
      arithmeticOriginalRevisedInfinityMap data H m j hj u hu =
        polynomialInitialInfinityInclusion (W.map q) (q (π ^ 1)) (q b3) (q b4) (q b6) ≫
          arithmeticOriginalRevisedAffineMap data H m j hj u hu := by
  exact factorRatioInfinityTargetMap_initial (W.map q) (H.a1_unit.map q) (q (π ^ 1)) τ
    (initialTangentSmoothing_factor (W.map q) (H.a1_unit.map q) (q (π ^ 1)))
    (q b3) (q b4) (q b6) r hr J (arithmeticParameterIdeal_nilpotent π m) hm
    (arithmeticCoefficient_mem π m (H.b3_div _)) c hc
    (arithmeticCoefficient_mem π m H.a2_div)
    (arithmeticCoefficient_mem π m (H.a3_div data))
    (arithmeticCoefficient_mem π m (H.a4_div data))
    (arithmeticCoefficient_mem π m (H.a6_div data)) _ _ _

end FLT.Mazur.WeierstrassDividedDepth
