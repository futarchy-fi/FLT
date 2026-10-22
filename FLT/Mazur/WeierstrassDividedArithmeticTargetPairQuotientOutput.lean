/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairCoverage

/-!
# Whole quotient-valued outputs on the three indexed target domains

Package the positive, negative and opposite formulas with their unchanged
arithmetic coefficient maps. These maps include the original nilpotents.
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

local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

omit [IsNoetherianRing R] in
/-- The whole tensor spectrum identification preserves the original coefficient map. -/
@[reassoc] theorem arithmeticTargetPairSpectrum_structure :
    (E).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) =
      pullback.fst f g ≫ f ≫ q := by
  have ha : Spec.map (CommRingCat.ofHom (successiveTensorPairLeft ei ej Q).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (successiveTensorPairLeft ei ej Q).commutes r
  rw [← ha, arithmeticTargetPairSpectrumIso_left_assoc]
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Q A)) ≫ q := by
    rw [← Spec.map_comp]
    congr 1
  rw [hb, arithmeticFixedAdjacentTargetCoordinates_structure_assoc]
  rfl

/-- Index the three genuine addition domains. -/
def arithmeticTargetPairOutputChart : Fin 3 → (pullback f g).Opens
  | 0 => arithmeticTargetPairPositiveOpen node data m k hk i j hi hj hij hdepth hsum h2
  | 1 => arithmeticTargetPairNegativeOpen node data m k hk i j hi hj hij hdepth hsum h2
  | 2 => arithmeticTargetPairOppositeOpen node data m k hk i j hi hj hij hsum

local notation "D" => arithmeticTargetPairOutputChart node data m k hk i j hi hj
  hij hdepth hsum h2

/-- Each indexed domain carries its existing whole resolved output. -/
def arithmeticTargetPairOutput : (b : Fin 3) → (D b).toScheme ⟶ (U).toScheme
  | 0 => arithmeticTargetPairPositiveAddition node data m k hk i j hi hj hij hdepth hsum h2
  | 1 => arithmeticTargetPairNegativeAddition node data m k hk i j hi hj hij hdepth hsum h2
  | 2 => arithmeticTargetPairOppositeAddition node data m k hk i j hi hj hij hsum

local notation "out" => arithmeticTargetPairOutput node data m k hk i j hi hj
  hij hdepth hsum h2

/-- All three formulas preserve the original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetPairOutput_structure (b : Fin 3) :
    out b ≫ t = (D b).ι ≫ pullback.fst f g ≫ f ≫ q := by
  fin_cases b <;>
    simp only [arithmeticTargetPairOutput, arithmeticTargetPairPositiveAddition,
      arithmeticTargetPairNegativeAddition, arithmeticTargetPairOppositeAddition,
      Category.assoc, successiveTensorPairPositiveAddition_structure,
      successiveTensorPairNegativeAddition_structure,
      successiveTensorPairOppositeAddition_structure, morphismRestrict_ι_assoc,
      arithmeticTargetPairSpectrum_structure node data m k hk i j hi hj] <;> rfl

/-- Each actual formula lifts over the entire original quotient. -/
def arithmeticTargetPairQuotientOutput (b : Fin 3) : (D b).toScheme ⟶ pullback q t :=
  pullback.lift ((D b).ι ≫ pullback.fst f g ≫ f) (out b)
    (by simpa only [Category.assoc] using
      (arithmeticTargetPairOutput_structure node data m k hk i j hi hj
        hij hdepth hsum h2 b).symm)

/-- The first projection retains all arithmetic coefficients. -/
@[reassoc] theorem arithmeticTargetPairQuotientOutput_base (b : Fin 3) :
    arithmeticTargetPairQuotientOutput node data m k hk i j hi hj hij hdepth hsum h2 b ≫
      pullback.fst q t = (D b).ι ≫ pullback.fst f g ≫ f := by
  simp only [arithmeticTargetPairQuotientOutput, pullback.lift_fst]

/-- The second projection retains the whole constructed resolved output. -/
@[reassoc] theorem arithmeticTargetPairQuotientOutput_integral (b : Fin 3) :
    arithmeticTargetPairQuotientOutput node data m k hk i j hi hj hij hdepth hsum h2 b ≫
      pullback.snd q t = out b := by
  simp only [arithmeticTargetPairQuotientOutput, pullback.lift_snd]

/-- The two punctures place the actual pair in one indexed formula domain. -/
theorem arithmeticTargetPairOutputChart_punctured (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hx : tensorCoord W (π ^ (0 + (i + 1))) π (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2 ∉
      (I (pullback.fst f g p)).asIdeal)
    (hy : tensorCoord W (π ^ (0 + (j + 1))) π (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2 ∉
      (J (pullback.snd f g p)).asIdeal) : ∃ b, p ∈ D b := by
  rcases arithmeticTargetPair_punctured_cover node data m k hk i j hi hj
    hij hdepth hsum h2 hlt p hx hy with hp | hp | hp
  · exact ⟨0, hp⟩
  · exact ⟨1, hp⟩
  · exact ⟨2, hp⟩

end FLT.Mazur.WeierstrassDividedDepth
