/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSourceTargetPairSpectrum
public import FLT.Mazur.WeierstrassDividedSuccessiveZeroMixedCoverage

/-!
# Zero/positive output using the adjacent target directly

The full source/target pair carries the unequal-depth resolved sum. Its
zero/positive domain covers punctured inputs through the middle depth without
requiring an additional atlas stage to reinterpret the target as a source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentSourceCoordinates arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j + 1) (hsum : i + (j + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "di" => data ⟨i,
  Nat.lt_succ_of_le ((Nat.le_add_right i 2).trans (hi.trans hk))⟩
local notation "dj" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "ei" => data ⟨i + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "E" => arithmeticSourceTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "V" => successiveTensorPairOppositeOpen hπ di ei dj ej Q
  (by change 0 + i ≤ 0 + (j + 1); omega) data k hk
    (by change (0 + i) + (0 + (j + 1)) ≤ k; omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "t" => (U).ι ≫ base

/-- The actual unequal-depth formula domain on both complete indexed source charts. -/
def arithmeticSourceTargetOppositeOpen : (pullback f g).Opens := (E).hom ⁻¹ᵁ V

local notation "D" => arithmeticSourceTargetOppositeOpen node data m k hk i j hi hj hij hsum

/-- The unequal-depth output keeps the supplied final resolved smooth model. -/
def arithmeticSourceTargetOppositeAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveTensorPairOppositeAddition hπ di ei dj ej Q
    (by change 0 + i ≤ 0 + (j + 1); omega) data k hk
    (by change (0 + i) + (0 + (j + 1)) ≤ k; omega)

/-- The entire resolved output preserves the original coefficient point. -/
@[reassoc] theorem arithmeticSourceTargetOppositeAddition_structure :
    arithmeticSourceTargetOppositeAddition node data m k hk i j hi hj hij hsum ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f g ≫ f ≫ q := by
  rw [arithmeticSourceTargetOppositeAddition, Category.assoc,
    successiveTensorPairOppositeAddition_structure, morphismRestrict_ι_assoc,
    arithmeticSourceTargetPairSpectrum_structure hπ data m k hk i j hi hj]
  rfl

/-- The actual formula output lies over the original arithmetic quotient. -/
def arithmeticSourceTargetOppositeQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f g ≫ f)
    (arithmeticSourceTargetOppositeAddition node data m k hk i j hi hj hij hsum)
    (by simpa only [Category.assoc] using
      (arithmeticSourceTargetOppositeAddition_structure node data m k hk i j hi hj hij hsum).symm)

/-- The first projection is exactly the original arithmetic coefficient map. -/
@[reassoc] theorem arithmeticSourceTargetOppositeQuotientOutput_base :
    arithmeticSourceTargetOppositeQuotientOutput node data m k hk i j hi hj hij hsum ≫
      pullback.fst q t = (D).ι ≫ pullback.fst f g ≫ f := by
  simp only [arithmeticSourceTargetOppositeQuotientOutput, pullback.lift_fst]

/-- The second projection is the full constructed unequal-depth sum. -/
@[reassoc] theorem arithmeticSourceTargetOppositeQuotientOutput_integral :
    arithmeticSourceTargetOppositeQuotientOutput node data m k hk i j hi hj hij hsum ≫
      pullback.snd q t =
        arithmeticSourceTargetOppositeAddition node data m k hk i j hi hj hij hsum := by
  simp only [arithmeticSourceTargetOppositeQuotientOutput, pullback.lift_snd]

local notation "u" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

/-- Every zero/positive punctured source pair up to middle depth has the actual output. -/
theorem arithmeticSourceTargetOpposite_zero_le_middle_mem
    (hz : i = 0) (hd : 2 * (j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal)
    (hy : v ∉ (J (pullback.snd f g p)).asIdeal) : p ∈ D := by
  apply successiveTensorPairOpposite_zero_le_middle_mem node di ei dj ej
    (by change 0 + i ≤ 0 + (j + 1); omega) data k hk
    (by change (0 + i) + (0 + (j + 1)) ≤ k; omega) m
    (by change 0 + i = 0; omega) (by change 0 < 0 + (j + 1); omega)
    (by change 2 * (0 + (j + 1)) ≤ depth; omega) ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourceTargetPairSpectrum_left_apply]
    exact hx
  · change v ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourceTargetPairSpectrum_right_apply]
    exact hy

end FLT.Mazur.WeierstrassDividedDepth
