/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSingleAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Constructed outputs on the mixed single-transfer source

Restrict the actual incidence transfer to the unchanged second puncture.
The three pulled-back addition domains cover this whole source and each carries
an explicit resolved smooth output morphism.
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
/-- Transport a three-way cover through a composite without expanding its scheme data. -/
theorem singleAddition_comp_preimage_cover {X Y Z : Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    (U V W : Z.Opens) (p : X) (h : b (a p) ∈ U ∨ b (a p) ∈ V ∨ b (a p) ∈ W) :
    p ∈ (a ≫ b) ⁻¹ᵁ U ∨ p ∈ (a ≫ b) ⁻¹ᵁ V ∨ p ∈ (a ≫ b) ⁻¹ᵁ W := h

/-- A composite principal-domain restriction retains its three successive point maps. -/
theorem singleAddition_preimage_three_mem {X Y Z T : Scheme}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) (U : T.Opens)
    (p : ((a ≫ b ≫ c) ⁻¹ᵁ U).toScheme) :
    c (b (a (((a ≫ b ≫ c) ⁻¹ᵁ U).ι p))) ∈ U := p.property

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

/-- The unchanged second puncture inside the actual first-incidence transfer domain. -/
def arithmeticRetainedSinglePuncturedOpen : ((D).toScheme).Opens :=
  ((D).ι ≫ pullback.snd f g ≫ J) ⁻¹ᵁ PrimeSpectrum.basicOpen v

local notation "F" => arithmeticRetainedSinglePuncturedOpen node data m k hk i j hi hj
local notation "input" => (F).ι ≫ T

/-- The positive addition domain on the actual single-transfer source. -/
def arithmeticRetainedSinglePositiveOpen : ((F).toScheme).Opens := input ⁻¹ᵁ O₊

/-- The negative addition domain on the actual single-transfer source. -/
def arithmeticRetainedSingleNegativeOpen : ((F).toScheme).Opens := input ⁻¹ᵁ O₋

/-- The opposite addition domain on the actual single-transfer source. -/
def arithmeticRetainedSingleOppositeOpen : ((F).toScheme).Opens := input ⁻¹ᵁ O₀

local notation "F₊" => arithmeticRetainedSinglePositiveOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "F₋" => arithmeticRetainedSingleNegativeOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "F₀" => arithmeticRetainedSingleOppositeOpen node data m k hk i j hi hj hij hsum

/-- The positive domain carries its constructed resolved smooth output. -/
def arithmeticRetainedSinglePositiveAddition : (F₊).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₊) ≫ arithmeticTargetPairPositiveAddition node data m k hk i j hi hj
    hij hdepth hsum h2

/-- The negative domain carries its constructed resolved smooth output. -/
def arithmeticRetainedSingleNegativeAddition : (F₋).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₋) ≫ arithmeticTargetPairNegativeAddition node data m k hk i j hi hj
    hij hdepth hsum h2

/-- The opposite domain carries its constructed unequal-depth resolved smooth output. -/
def arithmeticRetainedSingleOppositeAddition : (F₀).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₀) ≫ arithmeticTargetPairOppositeAddition node data m k hk i j hi hj hij hsum

/-- Every point in the actual mixed source belongs to a constructed output domain. -/
theorem arithmeticRetainedSingle_addition_cover (hlt : i < j) (p : (F).toScheme) :
    p ∈ F₊ ∨ p ∈ F₋ ∨ p ∈ F₀ := by
  apply singleAddition_comp_preimage_cover (F).ι T O₊ O₋ O₀ p
  exact arithmeticRetainedSingleTransfer_addition_cover node data m k hk i j hi hj hij
    hdepth hsum h2 hlt ((F).ι p)
    (singleAddition_preimage_three_mem (D).ι (pullback.snd f g) J
      (PrimeSpectrum.basicOpen v) p)

/-- The three actual output domains cover the complete incidence/puncture source. -/
theorem arithmeticRetainedSingle_addition_top (hlt : i < j) : F₊ ⊔ (F₋ ⊔ F₀) = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticRetainedSingle_addition_cover node data m k hk i j hi hj hij
    hdepth hsum h2 hlt p

end FLT.Mazur.WeierstrassDividedDepth
