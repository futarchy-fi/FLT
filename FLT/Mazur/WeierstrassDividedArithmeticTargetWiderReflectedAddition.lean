/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairPuncture
public import FLT.Mazur.WeierstrassDividedSuccessiveArithmeticWiderReflectedCoverage

/-!
# Constructed addition domains on full indexed arithmetic target pairs

The finite normalization supplies reflected outputs. Pull the three actual domains
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
  (hhi : depth < 2 * ((i + 1) + (j + 1)))
  (hstage : depth - (i + 1) - (j + 1) ≤ k)
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
  (by omega : depth - (0 + (i + 1)) - (0 + (j + 1)) ≤ k)
local notation "hl" => (by omega : (0 + (i + 1)) + 2 * (0 + (j + 1)) ≤ depth)
local notation "hm" => (by omega : depth ≤ 2 * ((0 + (i + 1)) + (0 + (j + 1))))
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "V₊" => successiveTensorWiderReflectedPositiveOpen node di ei dj ej Q hkl data
  k hk hs hl hm
local notation "V₋" => successiveTensorWiderReflectedNegativeOpen node di ei dj ej Q hkl data
  k hk hs hl hm
local notation "V₀" => successiveTensorWiderReflectedOppositeOpen node di ei dj ej Q hkl data
  k hk hs hl
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

/-- The positive reflected-depth domain on the actual indexed target pair. -/
def arithmeticTargetWiderReflectedPositiveOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₊

/-- The negative reflected-depth domain on the same indexed target pair. -/
def arithmeticTargetWiderReflectedNegativeOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₋

/-- The opposite-branch domain retaining both original depths. -/
def arithmeticTargetWiderReflectedOppositeOpen : (pullback (chart c ≫ s) (chart d ≫ s)).Opens :=
  (E).hom ⁻¹ᵁ V₀

/-- The positive domain carries the constructed smooth resolved output. -/
def arithmeticTargetWiderReflectedPositiveAddition :
    (arithmeticTargetWiderReflectedPositiveOpen node data m k hk i j hi hj
      hij hlo hhi hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₊) ≫
    successiveTensorWiderReflectedPositiveAddition node di ei dj ej Q hkl data k hk hs hl hm

/-- The negative domain carries the constructed smooth resolved output. -/
def arithmeticTargetWiderReflectedNegativeAddition :
    (arithmeticTargetWiderReflectedNegativeOpen node data m k hk i j hi hj
      hij hlo hhi hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₋) ≫
    successiveTensorWiderReflectedNegativeAddition node di ei dj ej Q hkl data k hk hs hl hm

/-- The opposite domain carries the constructed unequal-depth resolved output. -/
def arithmeticTargetWiderReflectedOppositeAddition :
    (arithmeticTargetWiderReflectedOppositeOpen node data m k hk i j hi hj
      hij hlo hstage).toScheme ⟶
      (U).toScheme :=
  ((E).hom ∣_ V₀) ≫
    successiveTensorWiderReflectedOppositeAddition node di ei dj ej Q hkl data k hk hs hl

end FLT.Mazur.WeierstrassDividedDepth
