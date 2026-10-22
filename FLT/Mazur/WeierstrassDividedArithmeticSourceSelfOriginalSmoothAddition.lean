/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSourcePairSpectrum
public import FLT.Mazur.WeierstrassDividedSuccessiveSelfOriginalSmoothAddition

/-!
# Original smooth outputs on full indexed arithmetic sources

The full unshifted source pair maps to its own-depth tensor construction.
At creation depth zero all punctured inputs have a quotient-valued resolved
output, including equal and self-inverse inputs.
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
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "di" => data ⟨i,
  Nat.lt_succ_of_le ((Nat.le_add_right i 2).trans (hi.trans hk))⟩
local notation "E" => arithmeticSourcePairSpectrumIso hπ data m k hk i i hi hi
local notation "A" => ScalarExtension W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "V" => successiveSelfOriginalSmoothOpen node di ei Q
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "f" => chart c ≫ s
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "P" => SuccessiveTensorPairRing ei ei Q

/-- The full equal-depth indexed source has the original smooth output domain. -/
def arithmeticSourceSelfOriginalSmoothOpen : (pullback f f).Opens := (E).hom ⁻¹ᵁ V

local notation "D" => arithmeticSourceSelfOriginalSmoothOpen node data m k hk i hi

/-- The original smooth output in the original final resolved smooth model. -/
def arithmeticSourceSelfOriginalSmoothAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveSelfOriginalSmoothAddition node di ei Q data k hk

/-- The entire original smooth output keeps the first arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSourceSelfOriginalSmoothAddition_structure :
    arithmeticSourceSelfOriginalSmoothAddition node data m k hk i hi ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f f ≫ f ≫ q := by
  rw [arithmeticSourceSelfOriginalSmoothAddition, Category.assoc,
    successiveSelfOriginalSmoothAddition_structure, morphismRestrict_ι_assoc,
    arithmeticSourcePairSpectrum_structure hπ data m k hk i i hi hi]
  rfl

local notation "t" => (U).ι ≫ base

/-- The original smooth output lies over the original quotient, including its nilpotents. -/
def arithmeticSourceSelfOriginalSmoothQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f f ≫ f)
    (arithmeticSourceSelfOriginalSmoothAddition node data m k hk i hi)
    (by simpa only [Category.assoc] using
      (arithmeticSourceSelfOriginalSmoothAddition_structure node data m k hk i hi).symm)

/-- The first projection is exactly the original smooth-domain coefficient map. -/
@[reassoc] theorem arithmeticSourceSelfOriginalSmoothQuotientOutput_base :
    arithmeticSourceSelfOriginalSmoothQuotientOutput node data m k hk i hi ≫
      pullback.fst q t =
      (D).ι ≫ pullback.fst f f ≫ f := by
  simp only [arithmeticSourceSelfOriginalSmoothQuotientOutput, pullback.lift_fst]

/-- The second projection is the entire constructed resolved addition. -/
@[reassoc] theorem arithmeticSourceSelfOriginalSmoothQuotientOutput_integral :
    arithmeticSourceSelfOriginalSmoothQuotientOutput node data m k hk i hi ≫
      pullback.snd q t =
        arithmeticSourceSelfOriginalSmoothAddition node data m k hk i hi := by
  simp only [arithmeticSourceSelfOriginalSmoothQuotientOutput, pullback.lift_snd]

local notation "u" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2

omit [IsNoetherianRing R] in
/-- Every punctured zero-created source pair has an actual original smooth output. -/
theorem arithmeticSourceSelfOriginalSmooth_zero_punctured (hz : i = 0) (hd : 0 < depth)
    (p : (pullback f f : Scheme))
    (hx : u ∉ (I (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (I (pullback.snd f f p)).asIdeal) : p ∈ D := by
  apply successiveSelfOriginalSmooth_zero_punctured node di ei m
    (by simpa only [Nat.zero_add] using hz) hd ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourcePairSpectrum_left_apply]
    exact hx
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticSourcePairSpectrum_right_apply]
    exact hy

end FLT.Mazur.WeierstrassDividedDepth
