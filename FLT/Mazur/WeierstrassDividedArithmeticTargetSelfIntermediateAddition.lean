/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedSuccessiveSelfIntermediateAddition

/-!
# Intermediate addition domains on equal indexed arithmetic targets

The full original self-product maps to the equal-depth tensor construction.
Both smooth outputs and the complete arithmetic coefficient morphism are retained.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hlo : 3 * (i + 1) ≤ depth) (hhi : depth < 4 * (i + 1))
  (hstage : (i + 1) + (depth - 3 * (i + 1)) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "di" => data ⟨i + 1, by omega⟩
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i i hi hi
local notation "A" => ScalarExtension W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "V" => successiveSelfIntermediateOpen node di ei Q data k hk
  (by simpa only [Nat.zero_add] using hlo)
  (by simpa only [Nat.zero_add] using hhi) (by simpa only [Nat.zero_add] using hstage)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "f" => chart c ≫ s
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "P" => SuccessiveTensorPairRing ei ei Q

/-- The full equal-depth indexed target has the genuine intermediate output domain. -/
def arithmeticTargetSelfIntermediateOpen : (pullback f f).Opens := (E).hom ⁻¹ᵁ V

local notation "D" => arithmeticTargetSelfIntermediateOpen node data m k hk i hi hlo hhi hstage
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi

/-- The intermediate output in the original final resolved smooth model. -/
def arithmeticTargetSelfIntermediateAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveSelfIntermediateAddition node di ei Q data k hk
    (by simpa only [Nat.zero_add] using hlo)
    (by simpa only [Nat.zero_add] using hhi) (by simpa only [Nat.zero_add] using hstage)

/-- The entire intermediate output keeps the first arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetSelfIntermediateAddition_structure :
    arithmeticTargetSelfIntermediateAddition node data m k hk i hi hlo hhi hstage ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f f ≫ f ≫ q := by
  rw [arithmeticTargetSelfIntermediateAddition, Category.assoc,
    successiveSelfIntermediateAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTargetSelfSpectrum_structure node data m k hk i hi]
  rfl

local notation "t" => (U).ι ≫ base

/-- The intermediate output lies over the original quotient, including its nilpotents. -/
def arithmeticTargetSelfIntermediateQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f f ≫ f)
    (arithmeticTargetSelfIntermediateAddition node data m k hk i hi hlo hhi hstage)
    (by simpa only [Category.assoc] using
      (arithmeticTargetSelfIntermediateAddition_structure node data m k hk i hi
        hlo hhi hstage).symm)

/-- The first projection is exactly the original intermediate-domain coefficient map. -/
@[reassoc] theorem arithmeticTargetSelfIntermediateQuotientOutput_base :
    arithmeticTargetSelfIntermediateQuotientOutput node data m k hk i hi hlo hhi hstage ≫
      pullback.fst q t = (D).ι ≫ pullback.fst f f ≫ f := by
  simp only [arithmeticTargetSelfIntermediateQuotientOutput, pullback.lift_fst]

/-- The second projection is the entire constructed resolved addition. -/
@[reassoc] theorem arithmeticTargetSelfIntermediateQuotientOutput_integral :
    arithmeticTargetSelfIntermediateQuotientOutput node data m k hk i hi hlo hhi hstage ≫
      pullback.snd q t =
        arithmeticTargetSelfIntermediateAddition node data m k hk i hi hlo hhi hstage := by
  simp only [arithmeticTargetSelfIntermediateQuotientOutput, pullback.lift_snd]

local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2

/-- Equal punctured indexed targets reach actual addition domains without branch premises. -/
theorem arithmeticTargetSelfIntermediate_punctured_cover
    (p : (pullback f f : Scheme))
    (hx : u ∉ (I (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (I (pullback.snd f f p)).asIdeal) : p ∈ D ∨ p ∈ C := by
  apply successiveSelfIntermediate_punctured_cover node di ei data k hk
    (by simpa only [Nat.zero_add] using hlo)
    (by simpa only [Nat.zero_add] using hhi) (by simpa only [Nat.zero_add] using hstage)
    m ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_left_apply]
    exact hx
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_right_apply]
    exact hy

end FLT.Mazur.WeierstrassDividedDepth
