/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentSource

/-!
# Full source-coordinate spectra including creation depth zero

The original retained source charts retain their common quotient coefficient
scheme before any transfer. Their tensor spectrum includes depth zero and
keeps both entire inputs and their nilpotent coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentSourceCoordinates arithmeticRetainedTensorIso
  olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n)

section SourceStructure
variable (i : ℕ) (hi : i + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 1, by omega⟩
local notation "A" => ScalarExtension W (π ^ (start + i)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "c" => (Fin.succ ⟨k - i, by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap Q A))

/-- The source coordinates preserve the full original quotient coefficient map. -/
@[reassoc] theorem arithmeticFixedAdjacentSourceCoordinates_structure :
    I ≫ a = chart c ≫ s := by
  have h := arithmeticRetainedTensorChart_structure hπ data m k hk i (by omega)
  unfold arithmeticRetainedTensorChart at h
  unfold arithmeticFixedAdjacentSourceCoordinates
  rw [← h, Category.assoc, Iso.inv_hom_id_assoc]

end SourceStructure

variable (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 1, by omega⟩
local notation "ej" => data ⟨j + 1, by omega⟩
local notation "A" => ScalarExtension W (π ^ (start + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "c" => (Fin.succ ⟨k - i, by omega⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap Q A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap Q B))
local notation "P" => SuccessiveTensorPairRing ei ej Q

/-- Product of the two actual coordinate isomorphisms over the arithmetic quotient. -/
def arithmeticSourcePairCoordinateIso : pullback (chart c ≫ s) (chart d ≫ s) ≅
    pullback a b :=
  asIso (pullback.map _ _ _ _ I J (𝟙 _) (by
    rw [Category.comp_id, arithmeticFixedAdjacentSourceCoordinates_structure]) (by
    rw [Category.comp_id, arithmeticFixedAdjacentSourceCoordinates_structure]))

/-- The full indexed pair is the spectrum of the full tensor pair over the quotient. -/
def arithmeticSourcePairSpectrumIso :
    pullback (chart c ≫ s) (chart d ≫ s) ≅ Spec (.of P) :=
  arithmeticSourcePairCoordinateIso hπ data m k hk i j hi hj ≪≫
    successiveTensorPairSpectrumIso ei ej Q

/-- The first original input is unchanged by the full spectrum identification. -/
@[reassoc] theorem arithmeticSourcePairSpectrumIso_left :
    (arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairLeft ei ej Q).toRingHom) =
        pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ I := by
  unfold arithmeticSourcePairSpectrumIso
  rw [Iso.trans_hom, Category.assoc, successiveTensorPairSpectrumIso_left]
  exact pullback.lift_fst _ _ _

/-- The second original input retains its independent creation depth. -/
@[reassoc] theorem arithmeticSourcePairSpectrumIso_right :
    (arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairRight ei ej Q).toRingHom) =
        pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ J := by
  unfold arithmeticSourcePairSpectrumIso
  rw [Iso.trans_hom, Category.assoc, successiveTensorPairSpectrumIso_right]
  exact pullback.lift_snd _ _ _

attribute [local irreducible] arithmeticSourcePairSpectrumIso arithmeticSourcePairCoordinateIso
  successiveTensorPairLeft successiveTensorPairRight

/-- The spectrum map retains the original coefficient morphism over the integral base. -/
@[reassoc] theorem arithmeticSourcePairSpectrum_structure :
    (arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R P)) =
        pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ chart c ≫ s ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Q)) := by
  have ha : Spec.map (CommRingCat.ofHom (successiveTensorPairLeft ei ej Q).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (successiveTensorPairLeft ei ej Q).commutes r
  rw [← ha, arithmeticSourcePairSpectrumIso_left_assoc]
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      a ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) := by
    rw [← Spec.map_comp]
    congr 1
  rw [hb, arithmeticFixedAdjacentSourceCoordinates_structure_assoc]

/-- The first tensor projection recovers the original source prime. -/
theorem arithmeticSourcePairSpectrum_left_apply
    (p : (pullback (chart c ≫ s) (chart d ≫ s) : Scheme)) :
    PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom
        ((arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom p) =
      I (pullback.fst (chart c ≫ s) (chart d ≫ s) p) := by
  have h := tensorPair_comap_of_factorization
    (arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom
    (successiveTensorPairLeft ei ej Q).toRingHom
    (pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ I)
    (arithmeticSourcePairSpectrumIso_left hπ data m k hk i j hi hj) p
  simp only [Scheme.Hom.comp_apply] at h
  convert! h using 1

/-- The second tensor projection recovers the independent original source prime. -/
theorem arithmeticSourcePairSpectrum_right_apply
    (p : (pullback (chart c ≫ s) (chart d ≫ s) : Scheme)) :
    PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom
        ((arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom p) =
      J (pullback.snd (chart c ≫ s) (chart d ≫ s) p) := by
  have h := tensorPair_comap_of_factorization
    (arithmeticSourcePairSpectrumIso hπ data m k hk i j hi hj).hom
    (successiveTensorPairRight ei ej Q).toRingHom
    (pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ J)
    (arithmeticSourcePairSpectrumIso_right hπ data m k hk i j hi hj) p
  simp only [Scheme.Hom.comp_apply] at h
  convert! h using 1

end FLT.Mazur.WeierstrassDividedDepth
