/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Addition domains after a single indexed retained transfer

The first factor moves from creation depth `i` to `i + 1`; the second factor
stays at `j + 1`. The actual target domains cover the transfer when the second
horizontal coordinate is nonzero. Numeric bounds concern those target depths.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j) (hdepth : 4 * (j + 1) ≤ depth)
  (hsum : (i + 1) + (j + 1) ≤ k) (h2 : W.a₂ = 0)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "O₊" => arithmeticTargetPairPositiveOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "O₋" => arithmeticTargetPairNegativeOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "O₀" => arithmeticTargetPairOppositeOpen node data m k hk i j hi hj hij hsum
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "oldIndex" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "oldCoords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "oldU" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 di) (Data.b4 di) (Data.b6 di) Q 2
local notation "f" => chart oldIndex ≫ s
local notation "f'" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "D" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi g
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk i hi g

/-- A single actual transfer reaches an addition domain if the unchanged input is punctured. -/
theorem arithmeticRetainedSingleTransfer_addition_cover (hlt : i < j)
    (p : (D).toScheme)
    (hy : v ∉ (J (pullback.snd f g ((D).ι p))).asIdeal) :
    T p ∈ O₊ ∨ T p ∈ O₋ ∨ T p ∈ O₀ := by
  apply arithmeticTargetPair_punctured_cover node data m k hk i j hi hj hij hdepth hsum h2
    hlt (T p) (arithmeticFixedAdjacentPairTransfer_punctured hπ data m k hk i hi g p)
  have he := congrArg (fun morphism => morphism p)
    (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk i hi g)
  change pullback.snd f' g (T p) = pullback.snd f g ((D).ι p) at he
  rw [he]
  exact hy

local instance arithmeticSingleAdditionCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The original nonpunctured/punctured mixed pair reaches a constructed output domain. -/
theorem arithmeticRetainedSingle_zero_addition_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hs : chart oldIndex (pullback.fst f g p) ∈ (s).smoothLocus)
    (hx : oldU ∈ (oldCoords (pullback.fst f g p)).asIdeal)
    (hy : v ∉ (J (pullback.snd f g p)).asIdeal) :
    ∃ q : (pullback f' g : Scheme),
      chart c (pullback.fst f' g q) = chart oldIndex (pullback.fst f g p) ∧
      pullback.snd f' g q = pullback.snd f g p ∧
      (q ∈ O₊ ∨ q ∈ O₋ ∨ q ∈ O₀) := by
  let z : (D).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
    hπ data node hgen m k hk i hi g (by omega) p hs hx⟩
  refine ⟨T z, ?_, ?_, arithmeticRetainedSingleTransfer_addition_cover
    node data m k hk i j hi hj hij hdepth hsum h2 hlt z hy⟩
  · exact congrArg (fun morphism => morphism z)
      (arithmeticFixedAdjacentPairTransfer_first hπ data m k hk i hi g)
  · exact congrArg (fun morphism => morphism z)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk i hi g)

end FLT.Mazur.WeierstrassDividedDepth
