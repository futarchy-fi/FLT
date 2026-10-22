/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSelfOriginalSmoothAddition
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfMixed

/-!
# Five complete outputs for the creation-zero self-pair at stage one

Use the original smooth law and two mixed formulas in each input order.
The mixed sources already cover double zero, so no additional source is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hi : 1 ≤ n)
local notation "j" => 0
local notation "hj" => hi
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj

variable (hm : 2 = depth)
local notation "V" => arithmeticRetainedSelfOriginalSmoothOpen node data m 1 hi 0
  (by omega)
local notation "MC" => arithmeticLastRetainedSelfMixedChart node data m j hj
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- One original smooth source and four ordered mixed sources. -/
abbrev LastRetainedZeroSelfLocalIndex := Unit ⊕ (Bool × Bool)

/-- All five sources are actual domains of already constructed whole outputs. -/
def arithmeticLastRetainedZeroSelfLocalSource : LastRetainedZeroSelfLocalIndex → Scheme
  | .inl _ => (V).toScheme
  | .inr (_, b) => (MC b).toScheme

local notation "X" => arithmeticLastRetainedZeroSelfLocalSource node data m hi

/-- The inclusions preserve the original input order, including the swapped mixed case. -/
def arithmeticLastRetainedZeroSelfLocalInclusion : (b : LastRetainedZeroSelfLocalIndex) →
    X b ⟶ pullback f f
  | .inl _ => (V).ι
  | .inr (false, b) => (MC b).ι ≫ (O).ι
  | .inr (true, b) => (MC b).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv

local notation "inc" => arithmeticLastRetainedZeroSelfLocalInclusion node data m hi

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedZeroSelfLocalInclusion_open (b : LastRetainedZeroSelfLocalIndex) :
    IsOpenImmersion (inc b) := by
  rcases b with b | ⟨b, label⟩
  · dsimp only [arithmeticLastRetainedZeroSelfLocalInclusion]
    infer_instance
  · cases b <;> dsimp only [arithmeticLastRetainedZeroSelfLocalInclusion] <;> infer_instance

/-- The full arithmetic quotient output on each of the five local domains. -/
def arithmeticLastRetainedZeroSelfLocalOutput : (b : LastRetainedZeroSelfLocalIndex) →
    X b ⟶ pullback q t
  | .inl _ => arithmeticRetainedSelfOriginalSmoothQuotientOutput
      node data m 1 hi 0 (by omega)
  | .inr (_, b) => arithmeticLastRetainedSelfMixedOutput node data m j hj hm b

/-- Every output preserves the complete original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfLocalOutput_base
    (b : LastRetainedZeroSelfLocalIndex) :
    arithmeticLastRetainedZeroSelfLocalOutput node data m hi hm b ≫ pullback.fst q t =
      inc b ≫ pullback.fst f f ≫ f := by
  rcases b with b | ⟨b, label⟩
  · exact arithmeticRetainedSelfOriginalSmoothQuotientOutput_base
      node data m 1 hi 0 (by omega)
  · cases b
    · simpa only [arithmeticLastRetainedZeroSelfLocalOutput,
        arithmeticLastRetainedZeroSelfLocalInclusion, Category.assoc] using
        arithmeticLastRetainedSelfMixedOutput_base node data m j hj hm label
    · change arithmeticLastRetainedSelfMixedOutput node data m j hj hm label ≫
        pullback.fst q t =
        ((MC label).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv) ≫ pullback.fst f f ≫ f
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc]
      exact arithmeticLastRetainedSelfMixedOutput_base_snd node data m j hj hm label

end FLT.Mazur.WeierstrassDividedDepth
