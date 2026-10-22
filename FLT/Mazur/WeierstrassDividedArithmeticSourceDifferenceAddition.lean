/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSourcePairSpectrum
public import FLT.Mazur.WeierstrassDividedSuccessiveDifferenceAddition

/-!
# Difference-stage outputs on full indexed arithmetic sources

The independent original source depths include zero. The opposite formula
retains the complete resolved output and the original quotient coefficients.
Opposite positive branches are covered below the fourfold bound without
requiring the final model to contain the sum of their depths.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentSourceCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "di" => data ⟨i,
  Nat.lt_succ_of_le ((Nat.le_add_right i 2).trans (hi.trans hk))⟩
local notation "dj" => data ⟨j,
  Nat.lt_succ_of_le ((Nat.le_add_right j 2).trans (hj.trans hk))⟩
local notation "ei" => data ⟨i + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "ej" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "E" => arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj
local notation "V" => successiveDifferenceOpen node di ei dj ej Q
  (by change 0 + i ≤ 0 + j; omega) data k hk
    (by change (0 + j) - (0 + i) ≤ k; omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "t" => (U).ι ≫ base

/-- The actual unequal-depth formula domain on both complete indexed source charts. -/
def arithmeticSourceDifferenceOpen : (pullback f g).Opens := (E).hom ⁻¹ᵁ V

local notation "D" => arithmeticSourceDifferenceOpen node data m k hk i j hi hj hij

/-- The unequal-depth output keeps the supplied final resolved smooth model. -/
def arithmeticSourceDifferenceAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveDifferenceAddition node di ei dj ej Q
    (by change 0 + i ≤ 0 + j; omega) data k hk
    (by change (0 + j) - (0 + i) ≤ k; omega)

/-- The entire resolved output preserves the original coefficient point. -/
@[reassoc] theorem arithmeticSourceDifferenceAddition_structure :
    arithmeticSourceDifferenceAddition node data m k hk i j hi hj hij ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f g ≫ f ≫ q := by
  rw [arithmeticSourceDifferenceAddition, Category.assoc,
    successiveDifferenceAddition_structure, morphismRestrict_ι_assoc,
    arithmeticSourcePairSpectrum_structure hπ data m k hk i j hi hj]
  rfl

/-- The actual formula output lies over the original arithmetic quotient. -/
def arithmeticSourceDifferenceQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f g ≫ f)
    (arithmeticSourceDifferenceAddition node data m k hk i j hi hj hij)
    (by simpa only [Category.assoc] using
      (arithmeticSourceDifferenceAddition_structure node data m k hk i j hi hj hij).symm)

/-- The first projection is exactly the original arithmetic coefficient map. -/
@[reassoc] theorem arithmeticSourceDifferenceQuotientOutput_base :
    arithmeticSourceDifferenceQuotientOutput node data m k hk i j hi hj hij ≫
      pullback.fst q t = (D).ι ≫ pullback.fst f g ≫ f := by
  simp only [arithmeticSourceDifferenceQuotientOutput, pullback.lift_fst]

/-- The second projection is the full constructed unequal-depth sum. -/
@[reassoc] theorem arithmeticSourceDifferenceQuotientOutput_integral :
    arithmeticSourceDifferenceQuotientOutput node data m k hk i j hi hj hij ≫
      pullback.snd q t =
        arithmeticSourceDifferenceAddition node data m k hk i j hi hj hij := by
  simp only [arithmeticSourceDifferenceQuotientOutput, pullback.lift_snd]

local notation "u" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "vi" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 1
local notation "vj" => tensorCoord W (π ^ (0 + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 1
local notation "A" => ScalarExtension W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (0 + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "P" => SuccessiveTensorPairRing ei ej Q
local notation "α" => algebraMap R A W.a₁
local notation "β" => algebraMap R B W.a₁

/-- Opposite full source branches require neither doubled data nor a sum-stage bound. -/
theorem arithmeticSourceDifference_opposite_mem
    (hi0 : 0 < i) (hlt : i < j) (hd : 2 * j < depth)
    (p : (pullback f g : Scheme))
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal)
    (hy : v ∉ (J (pullback.snd f g p)).asIdeal)
    (hb : (vi ∈ (I (pullback.fst f g p)).asIdeal ∧
        vj + β ∈ (J (pullback.snd f g p)).asIdeal) ∨
      (vi + α ∈ (I (pullback.fst f g p)).asIdeal ∧
        vj ∈ (J (pullback.snd f g p)).asIdeal)) : p ∈ D := by
  let z : PrimeSpectrum P := (E).hom p
  apply successiveDifference_opposite_slopes_mem node di ei dj ej
    (by change 0 + i ≤ 0 + j; omega) data k hk
    (by change (0 + j) - (0 + i) ≤ k; omega) m
    (by change 0 < 0 + i; omega) (by change 0 + i < 0 + j; omega)
    (by change 2 * (0 + j) < depth; omega) z
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourcePairSpectrum_left_apply]
    exact hx
  · change v ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourcePairSpectrum_right_apply]
    exact hy
  · rw [← arithmeticSourcePairSpectrum_left_apply hπ data m k hk i j hi hj p,
      ← arithmeticSourcePairSpectrum_right_apply hπ data m k hk i j hi hj p] at hb
    change ((successiveTensorPairLeft ei ej Q) vi ∈ z.asIdeal ∧
        (successiveTensorPairRight ei ej Q) (vj + β) ∈ z.asIdeal) ∨
      ((successiveTensorPairLeft ei ej Q) (vi + α) ∈ z.asIdeal ∧
        (successiveTensorPairRight ei ej Q) vj ∈ z.asIdeal) at hb
    have ha : (successiveTensorPairLeft ei ej Q) α = algebraMap R P W.a₁ :=
      (successiveTensorPairLeft ei ej Q).commutes W.a₁
    have hc : (successiveTensorPairRight ei ej Q) β = algebraMap R P W.a₁ :=
      (successiveTensorPairRight ei ej Q).commutes W.a₁
    simp only [map_add, ha, hc] at hb
    exact hb

end FLT.Mazur.WeierstrassDividedDepth
