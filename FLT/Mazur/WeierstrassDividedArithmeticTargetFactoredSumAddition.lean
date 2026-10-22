/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairPuncture
public import FLT.Mazur.WeierstrassDividedSuccessiveArithmeticFactoredSumCoverage

/-!
# Normalized sum-depth addition domains on indexed arithmetic pairs

The finite normalization supplies sum-depth outputs. Pull the three actual domains
back through the full spectrum identification, with both creation depths intact.
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
  (hij : i ≤ j) (hlo : (i + 1) + 2 * (j + 1) ≤ depth)
  (hstage : (i + 1) + (j + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "A" => ScalarExtension W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap Q A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap Q B))
local notation "P" => SuccessiveTensorPairRing ei ej Q

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "hkl" => (by omega : 0 + (i + 1) ≤ 0 + (j + 1))
local notation "hs" =>
  (by omega : (0 + (i + 1)) + (0 + (j + 1)) ≤ k)
local notation "hl" => (by omega : (0 + (i + 1)) + 2 * (0 + (j + 1)) ≤ depth)
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "V₊" => successiveTensorFactoredSumPositiveOpen node di ei dj ej Q hkl data
  k hk hs hl
local notation "V₋" => successiveTensorFactoredSumNegativeOpen node di ei dj ej Q hkl data
  k hk hs hl
local notation "V₀" => successiveTensorFactoredSumOppositeOpen node di ei dj ej Q hkl data
  k hk hs
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

/-- The positive sum-depth domain on the actual indexed target pair. -/
def arithmeticTargetFactoredSumPositiveOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₊

/-- The negative sum-depth domain on the same indexed target pair. -/
def arithmeticTargetFactoredSumNegativeOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₋

/-- The opposite-branch domain retaining both original depths. -/
def arithmeticTargetFactoredSumOppositeOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₀

/-- The positive domain carries the constructed smooth resolved output. -/
def arithmeticTargetFactoredSumPositiveAddition :
    (arithmeticTargetFactoredSumPositiveOpen node data m k hk i j hi hj
      hij hlo hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₊) ≫
    successiveTensorFactoredSumPositiveAddition node di ei dj ej Q hkl data k hk hs hl

/-- The negative domain carries the constructed smooth resolved output. -/
def arithmeticTargetFactoredSumNegativeAddition :
    (arithmeticTargetFactoredSumNegativeOpen node data m k hk i j hi hj
      hij hlo hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₋) ≫
    successiveTensorFactoredSumNegativeAddition node di ei dj ej Q hkl data k hk hs hl

/-- The opposite domain carries the constructed unequal-depth resolved output. -/
def arithmeticTargetFactoredSumOppositeAddition :
    (arithmeticTargetFactoredSumOppositeOpen node data m k hk i j hi hj
      hij hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₀) ≫
    successiveTensorFactoredSumOppositeAddition node di ei dj ej Q hkl data k hk hs

end FLT.Mazur.WeierstrassDividedDepth
