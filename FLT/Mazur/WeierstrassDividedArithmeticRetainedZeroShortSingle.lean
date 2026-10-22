/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSourceTargetZeroAddition
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondAdditionCoverage

/-!
# One-transfer outputs without an additional source chart

Transfer the first full input and keep the second unchanged, then use the
actual source/target zero/positive law at stage two. The output retains the original
quotient coefficients, including nilpotents. No coefficient normalization
or original nonzero abscissa is needed for the transferred input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentSourceCoordinates arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hsum : i + (i + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi f
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk i hi f
local notation "K" => T ≫ (pullbackSymmetry g f).hom
local notation "V" => arithmeticSourceTargetOppositeOpen node data m k hk i i
  hi hi (by omega) hsum
local notation "out" => arithmeticSourceTargetOppositeQuotientOutput node data m k hk i i
  hi hi (by omega) hsum
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The actual mixed output domain within the unchanged single-transfer source. -/
def arithmeticRetainedZeroShortSingleOpen : (O).toScheme.Opens := K ⁻¹ᵁ V

local notation "C" => arithmeticRetainedZeroShortSingleOpen node data m k hk i hi hsum

/-- The single-transfer formula has a genuine output over the original quotient. -/
def arithmeticRetainedZeroShortSingleOutput : (C).toScheme ⟶ pullback q t :=
  (K ∣_ V) ≫ out

/-- The output preserves the original first coefficient point through the transfer. -/
@[reassoc] theorem arithmeticRetainedZeroShortSingleOutput_base :
    arithmeticRetainedZeroShortSingleOutput node data m k hk i hi hsum ≫
      pullback.fst q t = (C).ι ≫ (O).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticRetainedZeroShortSingleOutput, Category.assoc,
    arithmeticSourceTargetOppositeQuotientOutput_base, morphismRestrict_ι_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rw [arithmeticFixedAdjacentPairTransfer_second_assoc, ← pullback.condition]
  rfl

/-- The same output preserves the second original coefficient point. -/
@[reassoc] theorem arithmeticRetainedZeroShortSingleOutput_base_snd :
    arithmeticRetainedZeroShortSingleOutput node data m k hk i hi hsum ≫
      pullback.fst q t = (C).ι ≫ (O).ι ≫ pullback.snd f f ≫ f := by
  rw [arithmeticRetainedZeroShortSingleOutput_base, pullback.condition]

/-- At creation depth zero only the unchanged second input needs a puncture. -/
theorem arithmeticRetainedZeroShortSingleOpen_mem (hz : i = 0) (hd : 2 ≤ depth)
    (p : (O).toScheme) (hu : u ∉ (I (pullback.snd f f ((O).ι p))).asIdeal) : p ∈ C := by
  apply arithmeticSourceTargetOpposite_zero_le_middle_mem node data m k hk i i
    hi hi (by omega) hsum hz (by omega) (K p)
  · change u ∉ (I (pullback.fst f g ((pullbackSymmetry g f).hom (T p)))).asIdeal
    rw [SchemePairSymmetryPoints.fst_apply]
    have he := congrArg (fun z => z p)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk i hi f)
    change pullback.snd g f (T p) = pullback.snd f f ((O).ι p) at he
    rw [he]
    exact hu
  · have hp := arithmeticFixedAdjacentPairTransfer_punctured hπ data m k hk i hi f p
    simpa only [Scheme.Hom.comp_apply, SchemePairSymmetryPoints.snd_apply] using hp

end FLT.Mazur.WeierstrassDividedDepth
