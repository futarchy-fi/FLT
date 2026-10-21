/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairAddition

/-!
# Coverage of full indexed targets and actual retained transfers

The two horizontal punctures imply one of the three constructed output domains.
On the actual retained transfer domain, both punctures follow from incidence.
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
  (hij : i ≤ j) (hdepth : 4 * (j + 1) ≤ depth)
  (hsum : (i + 1) + (j + 1) ≤ k) (h2 : W.a₂ = 0)
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
local notation "dd" => olderSumDepthDoubledData node (i + 1) (by omega)
local notation "ee" => olderSumDepthDoubledData node (j + 1) hdepth
local notation "hkl" => (by omega : 0 + (i + 1) ≤ 0 + (j + 1))
local notation "hs" => (by omega : (0 + (i + 1)) + (0 + (j + 1)) ≤ k)
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "V₊" => successiveTensorPairPositiveOpen hπ di ei dj ej Q hkl data
  k hk hs dd ee h2
local notation "V₋" => successiveTensorPairNegativeOpen hπ di ei dj ej Q hkl data
  k hk hs dd ee h2
local notation "V₀" => successiveTensorPairOppositeOpen hπ di ei dj ej Q hkl data k hk hs
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "O₊" => arithmeticTargetPairPositiveOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "O₋" => arithmeticTargetPairNegativeOpen node data m k hk i j hi hj
  hij hdepth hsum h2
local notation "O₀" => arithmeticTargetPairOppositeOpen node data m k hk i j hi hj hij hsum
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

/-- All horizontally punctured indexed target pairs have a constructed smooth output domain. -/
theorem arithmeticTargetPair_punctured_cover (hlt : i < j)
    (p : (pullback (chart c ≫ s) (chart d ≫ s) : Scheme))
    (hx : u ∉ (I (pullback.fst (chart c ≫ s) (chart d ≫ s) p)).asIdeal)
    (hy : v ∉ (J (pullback.snd (chart c ≫ s) (chart d ≫ s) p)).asIdeal) :
    p ∈ O₊ ∨ p ∈ O₋ ∨ p ∈ O₀ := by
  apply successiveArithmeticPair_punctured_cover node di ei dj ej m hkl data
    k hk hs dd ee h2 (by change 0 < 0 + (i + 1); omega)
    (by change 0 + (i + 1) < 0 + (j + 1); omega)
    (by change 2 * ((0 + (i + 1)) + (0 + (j + 1))) < depth; omega) ((E).hom p)
  · change u ∉ (PrimeSpectrum.comap (successiveTensorPairLeft ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_left_apply]
    exact hx
  · change v ∉ (PrimeSpectrum.comap (successiveTensorPairRight ei ej Q).toRingHom
      ((E).hom p)).asIdeal
    rw [arithmeticTargetPairSpectrum_right_apply]
    exact hy

local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj

/-- The actual simultaneous boundary domain needs no additional branch or puncture premises. -/
theorem arithmeticRetainedDoubleTransfer_addition_cover (hlt : i < j) (p : (D).toScheme) :
    t p ∈ O₊ ∨ t p ∈ O₋ ∨ t p ∈ O₀ := by
  have hp := arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj p
  exact arithmeticTargetPair_punctured_cover node data m k hk i j hi hj hij hdepth hsum h2
    hlt (t p) hp.1 hp.2

/-- Pulling the three actual output domains back covers the whole retained boundary domain. -/
theorem arithmeticRetainedDoubleTransfer_addition_top (hlt : i < j) :
    t ⁻¹ᵁ O₊ ⊔ (t ⁻¹ᵁ O₋ ⊔ t ⁻¹ᵁ O₀) = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticRetainedDoubleTransfer_addition_cover node data m k hk i j hi hj hij
    hdepth hsum h2 hlt p

end FLT.Mazur.WeierstrassDividedDepth
