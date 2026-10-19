/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalInfinityIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorInfinity
public import FLT.Mazur.WeierstrassInfinityFactorRatioIso
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioOverlapTorus
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioAtlasOverlap

/-!
# The full original infinity parameter in the depth-one diagonal atlas

The regular factor ratio identifies the entire original infinity cubic
with the torus at every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
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
local notation "hm" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (H.a1_unit.map q)
  (arithmeticCoefficient_mem π m H.a2_div) (arithmeticCoefficient_mem π m (H.b3_div _))
  (arithmeticCoefficient_mem π m (H.b4_div _)) (arithmeticCoefficient_mem π m (H.b6_div _))
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu
/-- The original specialized infinity cubic identifies the complete actual atlas open. -/
def arithmeticOneDiagonalInfinityOpenIso :
    Spec (.of (WeierstrassIntegralChart.Coordinate (W.map q) 1)) ≅ A .infinity :=
  arithmeticInfinityTensorIso π m W ≪≫
    arithmeticOneFiniteAtlasIso hπ data H m m hj u hu .infinity

/-- The full original infinity parameter is an isomorphism, including every arithmetic order. -/
def arithmeticOneDiagonalInfinityParameterIso : A .infinity ≅ branchTorus Q :=
  (arithmeticOneDiagonalInfinityOpenIso hπ data H m hj u hu).symm ≪≫
    infinityFactorRatioIso (W.map q) (H.a1_unit.map q) J
      (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m H.a2_div)
      (arithmeticCoefficient_mem π m (H.a3_div data))
      (arithmeticCoefficient_mem π m (H.a4_div data))
      (arithmeticCoefficient_mem π m (H.a6_div data)) (q (π ^ 1)) (q b3) r hm
      (arithmeticCoefficient_mem π m (H.b3_div _))

local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  b3 b4 b6 H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "E" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "d" => d₀

variable [IsBezout R]

/-- The complete infinity isomorphism restricts to the actual original overlap parameter. -/
@[reassoc] theorem arithmeticOneDiagonalInfinityParameterIso_overlap :
    i ≫ (E).hom = P := by
  simp only [arithmeticOneDiagonalOverlapToInfinity,
    arithmeticOneDiagonalInfinityParameterIso, arithmeticOneDiagonalInfinityOpenIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    infinityFactorRatioIso_hom]
  rw [← arithmeticFactorRatioOverlapInfinity_eq_atlas hπ data H m 2 hj]
  exact arithmeticFullInfinityRatioParameter_overlap π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.a3_div data) (H.a4_div data) (H.a6_div data)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

end FLT.Mazur.WeierstrassDividedDepth
