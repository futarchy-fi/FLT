/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedZeroSingleAddition
public import FLT.Mazur.WeierstrassDividedArithmeticSourceSelfOriginalSmoothAddition
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSelfPreMiddleTransfer

/-!
# Actual local outputs for creation-zero retained pairs

Five sources carry the original smooth law, both single-transfer orders,
and the two double-transfer laws. Each source is an actual open subchart
of the full original pair and every output retains its quotient coefficients.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)
  (hsum : (i + 1) + (i + 1) ≤ k) (hpre : 2 * (i + 1) < depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "V" => arithmeticSourceSelfOriginalSmoothOpen node data m k hk i hi
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i i hi hi
local notation "MC" => arithmeticRetainedZeroSingleOpen node data m k hk i hi hiNext (by omega)
local notation "MO" => arithmeticRetainedZeroSingleOutput node data m k hk i hi hiNext (by omega)
local notation "TC" => arithmeticRetainedSelfPreMiddleTransferChart node data m k hk
  i hi hsum hpre
local notation "TO" => arithmeticRetainedSelfPreMiddleTransferOutput node data m k hk
  i hi hsum hpre
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The five formula sources record both single-transfer orders separately. -/
abbrev RetainedZeroLocalIndex := Unit ⊕ (Bool ⊕ Bool)

/-- Each source is an actual formula open in the relevant full transfer source. -/
def arithmeticRetainedZeroLocalSource : RetainedZeroLocalIndex → Scheme
  | .inl _ => (V).toScheme
  | .inr (.inl _) => (MC).toScheme
  | .inr (.inr b) => (TC b).toScheme

local notation "X" => arithmeticRetainedZeroLocalSource node data m k hk i hi hiNext hsum hpre

/-- The inclusion records the original input order even in the reversed transfer. -/
def arithmeticRetainedZeroLocalInclusion : (b : RetainedZeroLocalIndex) → X b ⟶ pullback f f
  | .inl _ => (V).ι
  | .inr (.inl false) => (MC).ι ≫ (O).ι
  | .inr (.inl true) => (MC).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv
  | .inr (.inr b) => (TC b).ι ≫ (D).ι

local notation "inc" => arithmeticRetainedZeroLocalInclusion node data m k hk
  i hi hiNext hsum hpre

/-- Every local source is an open subchart of the original pair. -/
instance arithmeticRetainedZeroLocalInclusion_isOpenImmersion (b : RetainedZeroLocalIndex) :
    IsOpenImmersion (inc b) := by
  rcases b with b | (b | b)
  · dsimp only [arithmeticRetainedZeroLocalInclusion]
    infer_instance
  · cases b <;> dsimp only [arithmeticRetainedZeroLocalInclusion] <;> infer_instance
  · dsimp only [arithmeticRetainedZeroLocalInclusion]
    infer_instance

/-- Every source carries a constructed full sum over the original quotient. -/
def arithmeticRetainedZeroLocalOutput : (b : RetainedZeroLocalIndex) → X b ⟶ pullback q t
  | .inl _ => arithmeticSourceSelfOriginalSmoothQuotientOutput node data m k hk i hi
  | .inr (.inl _) => MO
  | .inr (.inr b) => TO b

/-- Each local output preserves its original source coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedZeroLocalOutput_base (b : RetainedZeroLocalIndex) :
    arithmeticRetainedZeroLocalOutput node data m k hk i hi hiNext hsum hpre b ≫
      pullback.fst q t = inc b ≫ pullback.fst f f ≫ f := by
  rcases b with b | (b | b)
  · exact arithmeticSourceSelfOriginalSmoothQuotientOutput_base node data m k hk i hi
  · cases b
    · simpa only [arithmeticRetainedZeroLocalOutput, arithmeticRetainedZeroLocalInclusion,
        Category.assoc] using arithmeticRetainedZeroSingleOutput_base
          node data m k hk i hi hiNext (by omega)
    · change MO ≫ pullback.fst q t =
        ((MC).ι ≫ (O).ι ≫ (pullbackSymmetry f f).inv) ≫ pullback.fst f f ≫ f
      rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst_assoc]
      exact arithmeticRetainedZeroSingleOutput_base_snd node data m k hk i hi hiNext (by omega)
  · simpa only [arithmeticRetainedZeroLocalOutput, arithmeticRetainedZeroLocalInclusion,
      Category.assoc] using arithmeticRetainedSelfPreMiddleTransferOutput_base
        node data m k hk i hi hsum hpre b

end FLT.Mazur.WeierstrassDividedDepth
