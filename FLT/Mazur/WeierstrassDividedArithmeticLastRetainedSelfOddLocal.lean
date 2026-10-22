/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfOddPunctured
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfOddMixed

/-!
# Twelve complete outputs for the equal last-retained odd pair

Use two punctured formulas and five mixed formulas in each input order.
The mixed families include the double-transfer sources. All sources embed into the original pair.
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



variable (hodd : depth = 2 * (i + 2) + 1)
local notation "V" => arithmeticLastRetainedSelfOddPuncturedChart node data m i hi hodd
local notation "MC" => arithmeticLastRetainedSelfOddMixedChart node data m j hj hodd (by omega)
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Two punctured formulas and ten ordered mixed sources, including double transfer. -/
abbrev LastRetainedSelfOddLocalIndex := Bool ⊕ (Bool × LastRetainedOddLocalIndex)

/-- All twelve sources are actual domains of already constructed whole outputs. -/
def arithmeticLastRetainedSelfOddLocalSource : LastRetainedSelfOddLocalIndex → Scheme
  | .inl b => (V b).toScheme
  | .inr (_, b) => (MC b).toScheme

local notation "X" => arithmeticLastRetainedSelfOddLocalSource node data m i hi hodd

/-- The inclusions preserve the original input order, including the swapped mixed case. -/
def arithmeticLastRetainedSelfOddLocalInclusion : (b : LastRetainedSelfOddLocalIndex) →
    X b ⟶ pullback f f
  | .inl b => (V b).ι
  | .inr (false, b) => (MC b).ι ≫ (O).ι
  | .inr (true, b) => (MC b).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv

local notation "inc" => arithmeticLastRetainedSelfOddLocalInclusion node data m i hi hodd

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedSelfOddLocalInclusion_open
    (b : LastRetainedSelfOddLocalIndex) :
    IsOpenImmersion (inc b) := by
  rcases b with b | ⟨b, label⟩
  · dsimp only [arithmeticLastRetainedSelfOddLocalInclusion]
    infer_instance
  · cases b <;> dsimp only [arithmeticLastRetainedSelfOddLocalInclusion] <;> infer_instance

/-- The full arithmetic quotient output on each of the twelve local domains. -/
def arithmeticLastRetainedSelfOddLocalOutput : (b : LastRetainedSelfOddLocalIndex) →
    X b ⟶ pullback q t
  | .inl b => arithmeticLastRetainedSelfOddPuncturedOutput node data m i hi hodd b
  | .inr (_, b) => arithmeticLastRetainedSelfOddMixedOutput node data m j hj hodd (by omega) b

/-- Every output preserves the complete original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedSelfOddLocalOutput_base
    (b : LastRetainedSelfOddLocalIndex) :
    arithmeticLastRetainedSelfOddLocalOutput node data m i hi hodd b ≫ pullback.fst q t =
      inc b ≫ pullback.fst f f ≫ f := by
  rcases b with b | ⟨b, label⟩
  · exact arithmeticLastRetainedSelfOddPuncturedOutput_base node data m i hi hodd b
  · cases b
    · simpa only [arithmeticLastRetainedSelfOddLocalOutput,
        arithmeticLastRetainedSelfOddLocalInclusion, Category.assoc] using
        arithmeticLastRetainedSelfOddMixedOutput_base node data m j hj hodd (by omega) label
    · change arithmeticLastRetainedSelfOddMixedOutput node data m j hj hodd (by omega) label ≫
        pullback.fst q t =
        ((MC label).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv) ≫ pullback.fst f f ≫ f
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc]
      exact arithmeticLastRetainedSelfOddMixedOutput_base_snd node data m j hj hodd (by omega) label

end FLT.Mazur.WeierstrassDividedDepth
