/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedSuccessiveSelfQuadrupleAddition

/-!
# Quadruple addition domains on equal indexed arithmetic targets

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
  (hsum : (i + 1) + (i + 1) ≤ k) (hquad : depth = 4 * (i + 1))
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
local notation "hs" => (by omega : (0 + (i + 1)) + (0 + (i + 1)) ≤ k)
local notation "A" => ScalarExtension W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "V" => successiveSelfQuadrupleOpen node di ei Q
  (by simpa only [Nat.zero_add] using hquad)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "f" => chart c ≫ s
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "P" => SuccessiveTensorPairRing ei ei Q

/-- The full equal-depth indexed target has the genuine quadruple output domain. -/
def arithmeticTargetSelfQuadrupleOpen : (pullback f f).Opens := (E).hom ⁻¹ᵁ V

local notation "D" => arithmeticTargetSelfQuadrupleOpen node data m k hk i hi hquad
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi

/-- The quadruple output in the original final resolved smooth model. -/
def arithmeticTargetSelfQuadrupleAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveSelfQuadrupleAddition node di ei Q data k hk hs
    (by simpa only [Nat.zero_add] using hquad)

/-- The entire quadruple output keeps the first arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetSelfQuadrupleAddition_structure :
    arithmeticTargetSelfQuadrupleAddition node data m k hk i hi hsum hquad ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f f ≫ f ≫ q := by
  rw [arithmeticTargetSelfQuadrupleAddition, Category.assoc,
    successiveSelfQuadrupleAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTargetSelfSpectrum_structure node data m k hk i hi]
  rfl

local notation "t" => (U).ι ≫ base

/-- The quadruple output lies over the original quotient, including its nilpotents. -/
def arithmeticTargetSelfQuadrupleQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f f ≫ f)
    (arithmeticTargetSelfQuadrupleAddition node data m k hk i hi hsum hquad)
    (by simpa only [Category.assoc] using
      (arithmeticTargetSelfQuadrupleAddition_structure node data m k hk i hi hsum hquad).symm)

/-- The first projection is exactly the original quadruple-domain coefficient map. -/
@[reassoc] theorem arithmeticTargetSelfQuadrupleQuotientOutput_base :
    arithmeticTargetSelfQuadrupleQuotientOutput node data m k hk i hi hsum hquad ≫
      pullback.fst q t =
      (D).ι ≫ pullback.fst f f ≫ f := by
  simp only [arithmeticTargetSelfQuadrupleQuotientOutput, pullback.lift_fst]

/-- The second projection is the entire constructed resolved addition. -/
@[reassoc] theorem arithmeticTargetSelfQuadrupleQuotientOutput_integral :
    arithmeticTargetSelfQuadrupleQuotientOutput node data m k hk i hi hsum hquad ≫
      pullback.snd q t =
        arithmeticTargetSelfQuadrupleAddition node data m k hk i hi hsum hquad := by
  simp only [arithmeticTargetSelfQuadrupleQuotientOutput, pullback.lift_snd]

local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2

/-- Equal punctured indexed targets reach actual addition domains without branch premises. -/
theorem arithmeticTargetSelfQuadruple_punctured_cover
    (p : (pullback f f : Scheme))
    (hx : u ∉ (I (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (I (pullback.snd f f p)).asIdeal) : p ∈ D ∨ p ∈ C := by
  apply successiveSelfQuadruple_punctured_cover node di ei
    (by simpa only [Nat.zero_add] using hquad) m
    (by change 0 < 0 + (i + 1); omega) ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_left_apply]
    exact hx
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_right_apply]
    exact hy

end FLT.Mazur.WeierstrassDividedDepth
