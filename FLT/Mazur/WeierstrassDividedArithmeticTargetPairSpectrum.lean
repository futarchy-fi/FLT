/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetStructure
public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPairSpectrum

/-!
# The indexed arithmetic target pair has its full original tensor spectrum

Both coordinate isomorphisms retain the common quotient coefficient scheme.
Their product therefore identifies the entire indexed pullback, not just its
residue points or a chosen open subset, with the full successive tensor pair.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, by omega⟩
local notation "ej" => data ⟨j + 2, by omega⟩
local notation "A" => ScalarExtension W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "c" => (Fin.succ ⟨k - (i + 1), by omega⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap Q A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap Q B))
local notation "P" => SuccessiveTensorPairRing ei ej Q

/-- Product of the two actual coordinate isomorphisms over the arithmetic quotient. -/
def arithmeticTargetPairCoordinateIso : pullback (chart c ≫ s) (chart d ≫ s) ≅
    pullback a b :=
  asIso (pullback.map _ _ _ _ I J (𝟙 _) (by
    rw [Category.comp_id, arithmeticFixedAdjacentTargetCoordinates_structure]) (by
    rw [Category.comp_id, arithmeticFixedAdjacentTargetCoordinates_structure]))

/-- The full indexed pair is the spectrum of the full tensor pair over the quotient. -/
def arithmeticTargetPairSpectrumIso :
    pullback (chart c ≫ s) (chart d ≫ s) ≅ Spec (.of P) :=
  arithmeticTargetPairCoordinateIso hπ data m k hk i j hi hj ≪≫
    successiveTensorPairSpectrumIso ei ej Q

/-- The first original input is unchanged by the full spectrum identification. -/
@[reassoc] theorem arithmeticTargetPairSpectrumIso_left :
    (arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairLeft ei ej Q).toRingHom) =
        pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ I := by
  unfold arithmeticTargetPairSpectrumIso
  rw [Iso.trans_hom, Category.assoc, successiveTensorPairSpectrumIso_left]
  exact pullback.lift_fst _ _ _

/-- The second original input retains its independent creation depth. -/
@[reassoc] theorem arithmeticTargetPairSpectrumIso_right :
    (arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj).hom ≫
      Spec.map (CommRingCat.ofHom (successiveTensorPairRight ei ej Q).toRingHom) =
        pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ J := by
  unfold arithmeticTargetPairSpectrumIso
  rw [Iso.trans_hom, Category.assoc, successiveTensorPairSpectrumIso_right]
  exact pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
