/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetWiderReflectedCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairQuotientOutput

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
  (hij : i ≤ j) (hlo : (i + 1) + 2 * (j + 1) ≤ depth)
  (hhi : depth < 2 * ((i + 1) + (j + 1)))
  (hstage : depth - (i + 1) - (j + 1) ≤ k)
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
local notation "hkl" => (by omega : 0 + (i + 1) ≤ 0 + (j + 1))
local notation "hs" =>
  (by omega : depth - (0 + (i + 1)) - (0 + (j + 1)) ≤ k)
local notation "hl" => (by omega : (0 + (i + 1)) + 2 * (0 + (j + 1)) ≤ depth)
local notation "hm" => (by omega : depth ≤ 2 * ((0 + (i + 1)) + (0 + (j + 1))))
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "V₊" => successiveTensorWiderReflectedPositiveOpen node di ei dj ej Q hkl data
  k hk hs hl hm
local notation "V₋" => successiveTensorWiderReflectedNegativeOpen node di ei dj ej Q hkl data
  k hk hs hl hm
local notation "V₀" => successiveTensorWiderReflectedOppositeOpen node di ei dj ej Q hkl data
  k hk hs hl
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Index the three genuine addition domains. -/
def arithmeticTargetWiderReflectedOutputChart : Fin 3 → (pullback f g).Opens
  | 0 => arithmeticTargetWiderReflectedPositiveOpen node data m k hk i j hi hj hij hlo hhi hstage
  | 1 => arithmeticTargetWiderReflectedNegativeOpen node data m k hk i j hi hj hij hlo hhi hstage
  | 2 => arithmeticTargetWiderReflectedOppositeOpen node data m k hk i j hi hj hij hlo hstage

local notation "D" => arithmeticTargetWiderReflectedOutputChart node data m k hk i j hi hj
  hij hlo hhi hstage

/-- Each indexed domain carries its existing whole resolved output. -/
def arithmeticTargetWiderReflectedOutput : (b : Fin 3) → (D b).toScheme ⟶ (U).toScheme
  | 0 => arithmeticTargetWiderReflectedPositiveAddition node data m k hk i j hi hj
      hij hlo hhi hstage
  | 1 => arithmeticTargetWiderReflectedNegativeAddition node data m k hk i j hi hj
      hij hlo hhi hstage
  | 2 => arithmeticTargetWiderReflectedOppositeAddition node data m k hk i j hi hj
      hij hlo hstage

local notation "out" => arithmeticTargetWiderReflectedOutput node data m k hk i j hi hj
  hij hlo hhi hstage

/-- All three formulas preserve the original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTargetWiderReflectedOutput_structure (b : Fin 3) :
    out b ≫ t = (D b).ι ≫ pullback.fst f g ≫ f ≫ q := by
  fin_cases b <;>
    simp only [arithmeticTargetWiderReflectedOutput, arithmeticTargetWiderReflectedPositiveAddition,
      arithmeticTargetWiderReflectedNegativeAddition,
      arithmeticTargetWiderReflectedOppositeAddition,
      Category.assoc, successiveTensorWiderReflectedPositiveAddition_structure,
      successiveTensorWiderReflectedNegativeAddition_structure,
      successiveTensorWiderReflectedOppositeAddition_structure, morphismRestrict_ι_assoc,
      arithmeticTargetPairSpectrum_structure node data m k hk i j hi hj] <;> rfl

/-- Each actual formula lifts over the entire original quotient. -/
def arithmeticTargetWiderReflectedQuotientOutput (b : Fin 3) : (D b).toScheme ⟶ pullback q t :=
  pullback.lift ((D b).ι ≫ pullback.fst f g ≫ f) (out b)
    (by simpa only [Category.assoc] using
      (arithmeticTargetWiderReflectedOutput_structure node data m k hk i j hi hj
        hij hlo hhi hstage b).symm)

/-- The first projection retains all arithmetic coefficients. -/
@[reassoc] theorem arithmeticTargetWiderReflectedQuotientOutput_base (b : Fin 3) :
    arithmeticTargetWiderReflectedQuotientOutput node data m k hk i j hi hj hij hlo hhi hstage b ≫
      pullback.fst q t = (D b).ι ≫ pullback.fst f g ≫ f := by
  simp only [arithmeticTargetWiderReflectedQuotientOutput, pullback.lift_fst]

/-- The second projection retains the whole constructed resolved output. -/
@[reassoc] theorem arithmeticTargetWiderReflectedQuotientOutput_integral (b : Fin 3) :
    arithmeticTargetWiderReflectedQuotientOutput node data m k hk i j hi hj hij hlo hhi hstage b ≫
      pullback.snd q t = out b := by
  simp only [arithmeticTargetWiderReflectedQuotientOutput, pullback.lift_snd]

/-- The two punctures place the actual pair in one indexed formula domain. -/
theorem arithmeticTargetWiderReflectedOutputChart_punctured (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hx : tensorCoord W (π ^ (0 + (i + 1))) π (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2 ∉
      (I (pullback.fst f g p)).asIdeal)
    (hy : tensorCoord W (π ^ (0 + (j + 1))) π (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2 ∉
      (J (pullback.snd f g p)).asIdeal) : ∃ b, p ∈ D b := by
  rcases arithmeticTargetWiderReflected_punctured_cover node data m k hk i j hi hj
    hij hlo hhi hstage hlt p hx hy with hp | hp | hp
  · exact ⟨0, hp⟩
  · exact ⟨1, hp⟩
  · exact ⟨2, hp⟩

end FLT.Mazur.WeierstrassDividedDepth
