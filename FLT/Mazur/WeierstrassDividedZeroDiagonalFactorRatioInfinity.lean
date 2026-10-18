/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioResidual
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorInfinity
public import FLT.Mazur.WeierstrassInfinityFactorRatioIso

/-!
# A full original infinity map for the corrected diagonal target

The regular factor ratio on the entire original infinity cubic is an isomorphism
onto the torus. Transport along the first initial boundary gives an open immersion
whose image covers the missing locus of both complete initial target nodes.
Agreement with the source initial restrictions is a separate gluing obligation.
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
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
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
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu
local notation "B" => arithmeticZeroDiagonalInitialInfinityBoundary hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu

/-- The original specialized infinity cubic identifies the complete actual atlas open. -/
def arithmeticZeroDiagonalInfinityOpenIso :
    Spec (.of (WeierstrassIntegralChart.Coordinate (W.map q) 1)) ≅ A .infinity :=
  arithmeticInfinityTensorIso π m W ≪≫
    arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu .infinity

/-- The full original infinity parameter is an isomorphism, including every arithmetic order. -/
def arithmeticZeroDiagonalInfinityParameterIso : A .infinity ≅ branchTorus Q :=
  (arithmeticZeroDiagonalInfinityOpenIso hπ data H m hj u hu).symm ≪≫
    infinityFactorRatioIso (W.map q) (H.a1_unit.map q) J
      (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m H.a2_div)
      (arithmeticCoefficient_mem π m (H.a3_div data))
      (arithmeticCoefficient_mem π m (H.a4_div data))
      (arithmeticCoefficient_mem π m (H.a6_div data)) (q (π ^ 1)) (q b3) r hm
      (arithmeticCoefficient_mem π m (H.b3_div _))

local notation "E" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu

/-- The entire actual infinity chart maps along the first full transported initial boundary. -/
def arithmeticZeroDiagonalFactorRatioInfinityMap :
    A .infinity ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu := (E).hom ≫ B false

local notation "g" => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu

instance arithmeticZeroDiagonalFactorRatioInfinityMap_isOpenImmersion :
    IsOpenImmersion g := by
  unfold arithmeticZeroDiagonalFactorRatioInfinityMap
  infer_instance

/-- The complete regular ratio, rather than a restricted overlap, defines the infinity map. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInfinityMap_transport :
    (arithmeticZeroDiagonalInfinityOpenIso hπ data H m hj u hu).hom ≫ g =
      infinityFactorRatioParameter (W.map q) J (arithmeticParameterIdeal_nilpotent π m)
        (arithmeticCoefficient_mem π m H.a2_div)
        (arithmeticCoefficient_mem π m (H.a3_div data))
        (arithmeticCoefficient_mem π m (H.a4_div data))
        (arithmeticCoefficient_mem π m (H.a6_div data)) (q (π ^ 1)) (q b3) r hm
        (arithmeticCoefficient_mem π m (H.b3_div _)) ≫ B false := by
  simp only [arithmeticZeroDiagonalFactorRatioInfinityMap,
    arithmeticZeroDiagonalInfinityParameterIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, infinityFactorRatioIso_hom]

attribute [local irreducible] arithmeticZeroDiagonalInfinityParameterIso
  arithmeticZeroDiagonalInfinityOpenIso

/-- The actual full infinity chart fills the entire transported boundary on either arm. -/
theorem arithmeticZeroDiagonalFactorRatioInfinityMap_range (b : Bool) :
    Set.range g = Set.range (B b) := by
  have h : Set.range g = Set.range (B false) := by
    change Set.range (B false ∘ (E).hom) = _
    have he : Function.Surjective (E).hom := (E).hom.homeomorph.surjective
    rw [Set.range_comp, he.range_eq, Set.image_univ]
  cases b
  · exact h
  · exact h.trans (arithmeticZeroDiagonalInitialInfinityBoundary_range hπ data H m hj u hu).symm

/-- Each whole initial target node is covered using the map on the full original infinity. -/
theorem arithmeticZeroDiagonalFactorRatioInitialInfinity_cover (b : Bool)
    (x : PolygonSmoothing.chart Q (s b)) :
    C b x ∈ Set.range (f b) ∨ C b x ∈ Set.range g := by
  rw [arithmeticZeroDiagonalFactorRatioInfinityMap_range hπ data H m hj u hu b]
  exact arithmeticZeroDiagonalInitialFactorRatio_cover hπ data H m hj u hu b x

/-- The full original infinity comparison reflects equality at every arithmetic order. -/
theorem arithmeticZeroDiagonalFactorRatioInfinityMap_injective : Function.Injective g :=
  (g).isOpenEmbedding.injective

end FLT.Mazur.WeierstrassDividedDepth
