/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfPunctured
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfMixed

/-!
# Seven complete outputs for the equal last-retained middle pair

Use two punctured formulas, two mixed formulas in each input order, and the
full double-transfer formula. All sources embed into the original pair.
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
  (m i : ℕ) (hi : i + 2 ≤ n)
local notation "j" => i + 1
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



variable (hm : 2 * (i + 2) = depth)
local notation "V" => arithmeticLastRetainedSelfPuncturedChart node data m i hi hm
local notation "MC" => arithmeticLastRetainedSelfMixedChart node data m j hj
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "O₂" => arithmeticLastRetainedDoubleOpen node data m j hj
local notation "D₂" => arithmeticLastRetainedDoubleMiddleSmoothOpen node data m j hj
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Two punctured, four ordered mixed, and one double-transfer source. -/
abbrev LastRetainedSelfLocalIndex := Bool ⊕ ((Bool × Bool) ⊕ Unit)

/-- All seven sources are actual domains of already constructed whole outputs. -/
def arithmeticLastRetainedSelfLocalSource : LastRetainedSelfLocalIndex → Scheme
  | .inl b => (V b).toScheme
  | .inr (.inl (_, b)) => (MC b).toScheme
  | .inr (.inr _) => (D₂).toScheme

local notation "X" => arithmeticLastRetainedSelfLocalSource node data m i hi hm

/-- The inclusions preserve the original input order, including the swapped mixed case. -/
def arithmeticLastRetainedSelfLocalInclusion : (b : LastRetainedSelfLocalIndex) →
    X b ⟶ pullback f f
  | .inl b => (V b).ι
  | .inr (.inl (false, b)) => (MC b).ι ≫ (O).ι
  | .inr (.inl (true, b)) => (MC b).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv
  | .inr (.inr _) => (D₂).ι ≫ (O₂).ι ≫ (O).ι

local notation "inc" => arithmeticLastRetainedSelfLocalInclusion node data m i hi hm

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedSelfLocalInclusion_open (b : LastRetainedSelfLocalIndex) :
    IsOpenImmersion (inc b) := by
  rcases b with b | (⟨b, label⟩ | b)
  · dsimp only [arithmeticLastRetainedSelfLocalInclusion]
    infer_instance
  · cases b <;> dsimp only [arithmeticLastRetainedSelfLocalInclusion] <;> infer_instance
  · dsimp only [arithmeticLastRetainedSelfLocalInclusion]
    infer_instance

/-- The full arithmetic quotient output on each of the seven local domains. -/
def arithmeticLastRetainedSelfLocalOutput : (b : LastRetainedSelfLocalIndex) →
    X b ⟶ pullback q t
  | .inl b => arithmeticLastRetainedSelfPuncturedOutput node data m i hi hm b
  | .inr (.inl (_, b)) => arithmeticLastRetainedSelfMixedOutput node data m j hj hm b
  | .inr (.inr _) => arithmeticLastRetainedDoubleMiddleQuotientOutput node data m j hj hm

/-- Every output preserves the complete original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedSelfLocalOutput_base (b : LastRetainedSelfLocalIndex) :
    arithmeticLastRetainedSelfLocalOutput node data m i hi hm b ≫ pullback.fst q t =
      inc b ≫ pullback.fst f f ≫ f := by
  rcases b with b | (⟨b, label⟩ | b)
  · exact arithmeticLastRetainedSelfPuncturedOutput_base node data m i hi hm b
  · cases b
    · simpa only [arithmeticLastRetainedSelfLocalOutput,
        arithmeticLastRetainedSelfLocalInclusion, Category.assoc] using
        arithmeticLastRetainedSelfMixedOutput_base node data m j hj hm label
    · change arithmeticLastRetainedSelfMixedOutput node data m j hj hm label ≫
        pullback.fst q t =
        ((MC label).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv) ≫ pullback.fst f f ≫ f
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc]
      exact arithmeticLastRetainedSelfMixedOutput_base_snd node data m j hj hm label
  · simpa only [arithmeticLastRetainedSelfLocalOutput,
      arithmeticLastRetainedSelfLocalInclusion, Category.assoc] using
      arithmeticLastRetainedDoubleMiddleQuotientOutput_base node data m j hj hm

end FLT.Mazur.WeierstrassDividedDepth
