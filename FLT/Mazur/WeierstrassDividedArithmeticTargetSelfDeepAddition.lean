/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairPuncture
public import FLT.Mazur.WeierstrassDividedSuccessiveSelfDeepAddition

/-!
# Deep addition domains on equal indexed arithmetic targets

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
  (hsum : (i + 1) + (i + 1) ≤ k)
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
local notation "V" => successiveSelfDeepOpen node di ei Q data k hk (by omega :
  (0 + (i + 1)) + (0 + (i + 1)) ≤ k)
local notation "Z" => successiveSelfReciprocalOpen node di ei Q
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "f" => chart c ≫ s
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "P" => SuccessiveTensorPairRing ei ei Q

/-- The full equal-depth indexed target has the genuine deep output domain. -/
def arithmeticTargetSelfDeepOpen : (pullback f f).Opens := (E).hom ⁻¹ᵁ V

/-- Its reciprocal companion retains the same complete target inputs. -/
def arithmeticTargetSelfReciprocalOpen : (pullback f f).Opens := (E).hom ⁻¹ᵁ Z

local notation "D" => arithmeticTargetSelfDeepOpen node data m k hk i hi hsum
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi

/-- The deep output in the original final resolved smooth model. -/
def arithmeticTargetSelfDeepAddition : (D).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ V) ≫ successiveSelfDeepAddition node di ei Q data k hk hs

/-- The reciprocal output in the same final model. -/
def arithmeticTargetSelfReciprocalAddition : (C).toScheme ⟶ (U).toScheme :=
  ((E).hom ∣_ Z) ≫ successiveSelfReciprocalAddition node di ei Q data k hk

omit [IsNoetherianRing R] in
/-- The full equal-target spectrum retains its original coefficient morphism. -/
@[reassoc] theorem arithmeticTargetSelfSpectrum_structure :
    (E).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) =
      pullback.fst f f ≫ f ≫ q := by
  have ha : Spec.map (CommRingCat.ofHom (successiveTensorPairLeft ei ei Q).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (successiveTensorPairLeft ei ei Q).commutes r
  rw [← ha, arithmeticTargetPairSpectrumIso_left_assoc]
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Q A)) ≫ q := by
    rw [← Spec.map_comp]
    congr 1
  rw [hb, arithmeticFixedAdjacentTargetCoordinates_structure_assoc]
  rfl

/-- The entire deep output keeps the first arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetSelfDeepAddition_structure :
    arithmeticTargetSelfDeepAddition node data m k hk i hi hsum ≫ (U).ι ≫ base =
      (D).ι ≫ pullback.fst f f ≫ f ≫ q := by
  rw [arithmeticTargetSelfDeepAddition, Category.assoc,
    successiveSelfDeepAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTargetSelfSpectrum_structure node data m k hk i hi]
  rfl

/-- The reciprocal output keeps the same original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetSelfReciprocalAddition_structure :
    arithmeticTargetSelfReciprocalAddition node data m k hk i hi ≫ (U).ι ≫ base =
      (C).ι ≫ pullback.fst f f ≫ f ≫ q := by
  rw [arithmeticTargetSelfReciprocalAddition, Category.assoc,
    successiveSelfReciprocalAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTargetSelfSpectrum_structure node data m k hk i hi]
  rfl

local notation "t" => (U).ι ≫ base

/-- The deep output lies over the original quotient, including its nilpotents. -/
def arithmeticTargetSelfDeepQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst f f ≫ f)
    (arithmeticTargetSelfDeepAddition node data m k hk i hi hsum)
    (by simpa only [Category.assoc] using
      (arithmeticTargetSelfDeepAddition_structure node data m k hk i hi hsum).symm)

/-- The reciprocal output also lies over the original quotient. -/
def arithmeticTargetSelfReciprocalQuotientOutput : (C).toScheme ⟶ pullback q t :=
  pullback.lift ((C).ι ≫ pullback.fst f f ≫ f)
    (arithmeticTargetSelfReciprocalAddition node data m k hk i hi)
    (by simpa only [Category.assoc] using
      (arithmeticTargetSelfReciprocalAddition_structure node data m k hk i hi).symm)

/-- The first projection is exactly the original deep-domain coefficient map. -/
@[reassoc] theorem arithmeticTargetSelfDeepQuotientOutput_base :
    arithmeticTargetSelfDeepQuotientOutput node data m k hk i hi hsum ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst f f ≫ f := by
  simp only [arithmeticTargetSelfDeepQuotientOutput, pullback.lift_fst]

/-- The first projection is exactly the original reciprocal-domain coefficient map. -/
@[reassoc] theorem arithmeticTargetSelfReciprocalQuotientOutput_base :
    arithmeticTargetSelfReciprocalQuotientOutput node data m k hk i hi ≫ pullback.fst q t =
      (C).ι ≫ pullback.fst f f ≫ f := by
  simp only [arithmeticTargetSelfReciprocalQuotientOutput, pullback.lift_fst]

local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2

/-- Equal punctured indexed targets reach actual addition domains without branch premises. -/
theorem arithmeticTargetSelfDeep_punctured_cover (hd : 4 * (i + 1) < depth)
    (p : (pullback f f : Scheme))
    (hx : u ∉ (I (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (I (pullback.snd f f p)).asIdeal) : p ∈ D ∨ p ∈ C := by
  apply successiveSelfDeep_punctured_cover node di ei data k hk hs m
    (by change 0 < 0 + (i + 1); omega)
    (by change 4 * (0 + (i + 1)) < depth; omega) ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_left_apply]
    exact hx
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ei Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_right_apply]
    exact hy

end FLT.Mazur.WeierstrassDividedDepth
