/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairSpectrum
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoublePuncture

/-!
# Both actual retained transfers are punctured in the full pair spectrum

Translate the two original target projections into prime-ideal contractions.
Both tensor horizontal coordinates are nonzero on every transferred point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticTargetPairSpectrumIso
  arithmeticTargetPairCoordinateIso arithmeticRetainedDoubleTransfer
/-- Evaluate a spectrum factorization without unfolding the source scheme. -/
theorem tensorPair_comap_of_factorization {X : Scheme} {A B : Type}
    [CommRing A] [CommRing B] (f : X ⟶ Spec (.of B)) (g : A →+* B)
    (h : X ⟶ Spec (.of A)) (he : f ≫ Spec.map (CommRingCat.ofHom g) = h) (p : X) :
    PrimeSpectrum.comap g (f p) = h p :=
  congrArg (fun q => q p) he

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "A" => ScalarExtension W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (start + (j + 1))) π
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

local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "u" => tensorCoord W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

/-- Prime contraction along the first tensor inclusion is the original first target point. -/
theorem arithmeticTargetPairSpectrum_left_apply
    (p : (pullback (chart c ≫ s) (chart d ≫ s) : Scheme)) :
    PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom ((E).hom p) =
      I (pullback.fst (chart c ≫ s) (chart d ≫ s) p) := by
  have h := tensorPair_comap_of_factorization (E).hom
    (successiveTensorPairLeft ei ej Q).toRingHom
    (pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ I)
    (arithmeticTargetPairSpectrumIso_left hπ data m k hk i j hi hj) p
  simp only [Scheme.Hom.comp_apply] at h
  convert! h using 1

/-- Prime contraction along the second inclusion is the original independent target point. -/
theorem arithmeticTargetPairSpectrum_right_apply
    (p : (pullback (chart c ≫ s) (chart d ≫ s) : Scheme)) :
    PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom ((E).hom p) =
      J (pullback.snd (chart c ≫ s) (chart d ≫ s) p) := by
  have h := tensorPair_comap_of_factorization (E).hom
    (successiveTensorPairRight ei ej Q).toRingHom
    (pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ J)
    (arithmeticTargetPairSpectrumIso_right hπ data m k hk i j hi hj) p
  simp only [Scheme.Hom.comp_apply] at h
  convert! h using 1

/-- Both exact horizontal coordinates avoid the prime of every actual transferred pair. -/
theorem arithmeticRetainedDoubleTransfer_tensor_punctured (p : (D).toScheme) :
    successiveTensorPairLeft ei ej Q u ∉ ((E).hom (t p)).asIdeal ∧
      successiveTensorPairRight ei ej Q v ∉ ((E).hom (t p)).asIdeal := by
  have hp := arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj p
  constructor
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom
      ((E).hom (t p))).asIdeal
    rw [arithmeticTargetPairSpectrum_left_apply]
    exact hp.1
  · change v ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom
      ((E).hom (t p))).asIdeal
    rw [arithmeticTargetPairSpectrum_right_apply]
    exact hp.2

end FLT.Mazur.WeierstrassDividedDepth
