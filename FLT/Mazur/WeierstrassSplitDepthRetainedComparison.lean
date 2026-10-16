/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthStartOneAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticStartOneRetained

/-!
# Retained comparisons constructed from the original split depth

The data, coefficient hypotheses, quotient units and correction factors are
all constructed from the original curve. The full adjacent edges and original
arithmetic quotient squares hold at every retained label of this depth-one model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (n : ℕ) (hn : 2 * (1 + n) < depth) (m k : ℕ) (hk : k ≤ n)
local notation "d" => splitDepthStartOneData D n hn
local notation "H" => splitDepthStartOneAtlasCoefficients D n hn

/-- The actual full retained-node map for the constructed depth-one split model. -/
def splitDepthRetainedComparison (a : Fin k) (b : Bool) :
    arithmeticLabeledAtlasObject D.uniformizer_ne_zero d H m k hk (.retained a b) ⟶
      arithmeticFactorRatioPolygon π m W (π ^ 1) (H).a1_unit (H).scale_div k :=
  arithmeticStartOneRetainedMap D.uniformizer_ne_zero d H m k hk a b

omit [IsBezout R] in
/-- Both labels satisfy the entire adjacent-edge equation from the split coefficients. -/
@[reassoc] theorem splitDepthRetainedComparison_adjacent
    (a : ℕ) (ha : a + 1 < k) (b : Bool) :
    leftBranchOpen (Quotient R π m) (parameter R π m) ≫
        splitDepthRetainedComparison D n hn m k hk ⟨a, by omega⟩ b =
      precedingBranch (Quotient R π m) (parameter R π m) ≫
        splitDepthRetainedComparison D n hn m k hk ⟨a + 1, ha⟩ b :=
  arithmeticStartOneRetainedMap_adjacent D.uniformizer_ne_zero d H m k hk a ha b

omit [IsBezout R] in
/-- The constructed maps retain the original arithmetic restriction at every label. -/
@[reassoc] theorem splitDepthRetainedComparison_restriction (a : Fin k) (b : Bool) :
    splitDepthRetainedComparison D n hn m k hk a b ≫
        arithmeticFactorRatioPolygonRestriction π m W (π ^ 1) (H).a1_unit (H).scale_div k =
      arithmeticLabeledAtlasRestriction D.uniformizer_ne_zero d H m k hk (.retained a b) ≫
        splitDepthRetainedComparison D n hn (m + 1) k hk a b :=
  arithmeticStartOneRetainedMap_restriction D.uniformizer_ne_zero d H m k hk a b

omit [IsBezout R] in
/-- The first node keeps the independently constructed original factor-ratio map. -/
theorem splitDepthRetainedComparison_first (hk0 : 0 < k) (b : Bool) :
    splitDepthRetainedComparison D n hn m k hk ⟨0, hk0⟩ b =
      arithmeticFactorRatioFirstRetainedMap D.uniformizer_ne_zero d H m k hk hk0 b :=
  arithmeticStartOneRetainedMap_first D.uniformizer_ne_zero d H m k hk hk0 b

end FLT.Mazur.WeierstrassDividedDepth
