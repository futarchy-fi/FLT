/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFactorRatioAffineTarget
public import FLT.Mazur.WeierstrassDividedRevisedInitialMaps

/-!
# The entire original arithmetic affine chart in the revised polygon

The canonical polynomial root and the actual quotient ideal supply the full
factor-ratio gluing at every order. Both original node labels are recovered.
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

/-- The complete original affine coordinate scheme maps to the independently glued polygon. -/
def arithmeticOriginalRevisedAffineMap :
    Spec (.of (ExtendedCoordinate W (π ^ 1) b3 b4 b6 Q)) ⟶
      arithmeticRevisedPolygon data H m j hj u hu :=
  factorRatioAffineTargetMap (W.map q) (H.a1_unit.map q) (q (π ^ 1)) τ
    (initialTangentSmoothing_factor (W.map q) (H.a1_unit.map q) (q (π ^ 1)))
    (q b3) (q b4) (q b6) r hr J (arithmeticParameterIdeal_nilpotent π m) hm
    (arithmeticCoefficient_mem π m (H.b3_div _)) c hc

/-- Both whole original node charts recover their already constructed revised initial maps. -/
@[reassoc] theorem arithmeticOriginalRevisedAffineMap_chart (b : Bool) :
    (if b then arithmeticOppositeInitialNodeChart π m W (π ^ 1) b3 b4 b6 H.a1_unit
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      else arithmeticInitialNodeChart π m W (π ^ 1) b3 b4 b6 H.a1_unit
        H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)) ≫
        arithmeticOriginalRevisedAffineMap data H m j hj u hu =
      arithmeticOriginalRevisedInitialMap data H m j hj u hu b := by
  have h := factorRatioAffineTargetMap_chart (W.map q) (H.a1_unit.map q) (q (π ^ 1)) τ
    (initialTangentSmoothing_factor (W.map q) (H.a1_unit.map q) (q (π ^ 1)))
    (q b3) (q b4) (q b6) r hr J (arithmeticParameterIdeal_nilpotent π m) hm
    (arithmeticCoefficient_mem π m (H.b3_div _)) c hc b
  cases b <;> exact h

/-- The two actual original node-overlap maps agree in the independently glued target. -/
@[reassoc] theorem arithmeticOriginalRevisedInitialMap_overlap :
    polynomialNodeOverlapInclusion (W.map q) (q (π ^ 1)) ≫
        arithmeticOriginalRevisedInitialMap data H m j hj u hu false =
      arithmeticNodeOverlapOpposite π m W (π ^ 1) b3 b4 b6 H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _) ≫
          arithmeticOriginalRevisedInitialMap data H m j hj u hu true := by
  exact factorRatioNodeTargetMap_overlap (W.map q) (H.a1_unit.map q) (q (π ^ 1)) τ
    (initialTangentSmoothing_factor (W.map q) (H.a1_unit.map q) (q (π ^ 1)))
    (q b3) (q b4) (q b6) r hr J (arithmeticParameterIdeal_nilpotent π m) hm
    (arithmeticCoefficient_mem π m (H.b3_div _)) c hc

end FLT.Mazur.WeierstrassDividedDepth
