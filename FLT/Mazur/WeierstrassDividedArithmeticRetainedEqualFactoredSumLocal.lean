/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSelfFlexibleTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSelfFactoredSumMixed

/-!
# Equal-retained outputs beyond the mixed-input sum middle

The ten charts consist of two unshifted formulas, three formulas in each
single-transfer order, and two double-transfer formulas. Every chart is an
actual open immersion into the original pair and carries a quotient output.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)
  (hdeep : 2 * ((i + 1) + (i + 2)) < depth)
  (hstage : min (2 * (i + 2)) (depth - 2 * (i + 2)) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "V" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m k hk i hi
  (by omega) (by omega)
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) (i + 1) hiNext hiNext
local notation "MC" => arithmeticRetainedSelfFactoredSumMixedChart node data m k hk i hi hiNext
  (by omega) (by omega)
local notation "MO" => arithmeticRetainedSelfFactoredSumMixedOutput node data m k hk i hi hiNext
  (by omega) (by omega)
local notation "TC" => arithmeticRetainedSelfFlexiblePreMiddleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "TO" => arithmeticRetainedSelfFlexiblePreMiddleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Indices distinguish both single-transfer orders and all genuine formulas. -/
abbrev RetainedEqualFactoredSumLocalIndex := Bool ⊕ ((Bool × Fin 3) ⊕ Bool)

/-- Each local source is an actual formula open in its unchanged transfer source. -/
def arithmeticRetainedEqualFactoredSumLocalSource :
    RetainedEqualFactoredSumLocalIndex → Scheme
  | .inl false => (V).toScheme
  | .inl true => (Z).toScheme
  | .inr (.inl (_, b)) => (MC b).toScheme
  | .inr (.inr b) => (TC b).toScheme

local notation "X" => arithmeticRetainedEqualFactoredSumLocalSource node data m k hk i hi hiNext
  hdeep hstage

/-- The inclusion remembers the original order of both input factors. -/
def arithmeticRetainedEqualFactoredSumLocalInclusion :
    (b : RetainedEqualFactoredSumLocalIndex) →
    X b ⟶ pullback f f
  | .inl false => (V).ι
  | .inl true => (Z).ι
  | .inr (.inl (false, b)) => (MC b).ι ≫ (O).ι
  | .inr (.inl (true, b)) => (MC b).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv
  | .inr (.inr b) => (TC b).ι ≫ (D).ι

local notation "inc" => arithmeticRetainedEqualFactoredSumLocalInclusion
  node data m k hk i hi hiNext hdeep hstage

/-- The sources are genuine open subcharts of the full original arithmetic pair. -/
instance arithmeticRetainedEqualFactoredSumLocalInclusion_isOpenImmersion
    (b : RetainedEqualFactoredSumLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with b | (⟨b, label⟩ | b)
  · cases b <;> dsimp only [arithmeticRetainedEqualFactoredSumLocalInclusion] <;> infer_instance
  · cases b <;> dsimp only [arithmeticRetainedEqualFactoredSumLocalInclusion] <;> infer_instance
  · dsimp only [arithmeticRetainedEqualFactoredSumLocalInclusion]
    infer_instance

/-- The output on every chart is one of the constructed full quotient-valued formulas. -/
def arithmeticRetainedEqualFactoredSumLocalOutput : (b : RetainedEqualFactoredSumLocalIndex) →
    X b ⟶ pullback q t
  | .inl false => arithmeticTargetSelfFlexiblePreMiddleQuotientOutput node data m k hk i hi
      (by omega) (by omega)
  | .inl true => arithmeticTargetSelfReciprocalQuotientOutput node data m k hk i hi
  | .inr (.inl (_, b)) => MO b
  | .inr (.inr b) => TO b

/-- Every local output keeps the original coefficient morphism through its source inclusion. -/
@[reassoc] theorem arithmeticRetainedEqualFactoredSumLocalOutput_base
    (b : RetainedEqualFactoredSumLocalIndex) :
    arithmeticRetainedEqualFactoredSumLocalOutput node data m k hk i hi hiNext hdeep hstage b ≫
      pullback.fst q t = inc b ≫ pullback.fst f f ≫ f := by
  rcases b with b | (⟨b, label⟩ | b)
  · cases b
    · exact arithmeticTargetSelfFlexiblePreMiddleQuotientOutput_base node data m k hk i hi
        (by omega) (by omega)
    · exact arithmeticTargetSelfReciprocalQuotientOutput_base node data m k hk i hi
  · cases b
    · simpa only [arithmeticRetainedEqualFactoredSumLocalOutput,
        arithmeticRetainedEqualFactoredSumLocalInclusion, Category.assoc] using
        arithmeticRetainedSelfFactoredSumMixedOutput_base node data m k hk i hi hiNext
          (by omega) (by omega) label
    · change MO label ≫ pullback.fst q t =
        ((MC label).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv) ≫ pullback.fst f f ≫ f
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc]
      exact arithmeticRetainedSelfFactoredSumMixedOutput_base_snd node data m k hk i hi hiNext
        (by omega) (by omega) label
  · simpa only [arithmeticRetainedEqualFactoredSumLocalOutput,
      arithmeticRetainedEqualFactoredSumLocalInclusion, Category.assoc] using
      arithmeticRetainedSelfFlexiblePreMiddleTransferOutput_base node data m k hk
        (i + 1) hiNext (by omega) (by omega) b

end FLT.Mazur.WeierstrassDividedDepth
