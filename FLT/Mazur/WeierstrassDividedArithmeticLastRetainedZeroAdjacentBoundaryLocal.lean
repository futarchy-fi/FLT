/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentSelfFlexibleTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMixedZeroBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticSourceTargetZeroAddition

/-!
# Creation-zero adjacent boundary pairs at final stage two

At node depth four or five, combine the direct opposite formula, two self
formulas after the earlier transfer, and four complete last-transfer sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hk : 2 ≤ n)
  (hdepth : 4 ≤ depth) (hnear : depth ≤ 5)
local notation "k" => 2
local notation "hi" => (Nat.le_refl 2)
local notation "hj" => (Nat.le_refl 2)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨1, Nat.lt_succ_of_le ((Nat.le_trans
  (Nat.le_succ 1) hi).trans hk)⟩
local notation "ej" => data ⟨2, Nat.lt_succ_of_le hk⟩
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - 1,
  Nat.lt_succ_of_le ((Nat.sub_le k 1).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk 0 hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk 0 hj

local notation "u" => tensorCoord W (π ^ (0 + 0)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + 1)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticSourceTargetOppositeOpen node data m k hk 0 0 hi hj
  (by omega) (by omega)
local notation "SC" => arithmeticRetainedAdjacentSelfFlexibleTransferChart node data m k hk
  0 hi (by omega) (by omega)
local notation "SO" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput node data m k hk
  0 hi (by omega) (by omega)
local notation "MC" => arithmeticLastRetainedMixedZeroBoundaryChart node data m 1 hk
  0 (by omega) hdepth hnear
local notation "MO" => arithmeticLastRetainedMixedZeroBoundaryOutput node data m 1 hk
  0 (by omega) hdepth hnear
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk 0 hi g
local notation "T" => arithmeticLastRetainedPairOpen node data m 1 hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- One unshifted domain, two earlier-transfer domains, and the last-transfer sources. -/
abbrev LastRetainedZeroAdjacentBoundaryLocalIndex :=
  Unit ⊕ (Bool ⊕ MixedZeroBoundaryNodalLocalIndex)

/-- Actual open domains inside the original pair or its incidence source. -/
def arithmeticLastRetainedZeroAdjacentBoundaryLocalSource :
    LastRetainedZeroAdjacentBoundaryLocalIndex → Scheme
  | .inl _ => (V).toScheme
  | .inr (.inl b) => (SC b).toScheme
  | .inr (.inr b) => (MC b).toScheme

local notation "X" => arithmeticLastRetainedZeroAdjacentBoundaryLocalSource
  node data m hk hdepth hnear

/-- Each source embeds into the complete original ordered pair. -/
def arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion :
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) → X b ⟶ pullback f g
  | .inl _ => (V).ι
  | .inr (.inl b) => (SC b).ι ≫ (S).ι
  | .inr (.inr b) => (MC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv

local notation "inc" => arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion
  node data m hk hdepth hnear

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion_open
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with b | (b | b) <;>
    dsimp only [arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion] <;> infer_instance

/-- All sources carry whole arithmetic quotient outputs. -/
def arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput :
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) → X b ⟶ pullback q t
  | .inl _ => arithmeticSourceTargetOppositeQuotientOutput
      node data m k hk 0 0 hi hj (by omega) (by omega)
  | .inr (.inl b) => SO b
  | .inr (.inr b) => MO b

/-- The output retains the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput_base
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput
      node data m hk hdepth hnear b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with b | (b | b)
  · exact arithmeticSourceTargetOppositeQuotientOutput_base
      node data m k hk 0 0 hi hj (by omega) (by omega)
  · simpa only [arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput,
      arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion, Category.assoc] using
      arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base
        node data m k hk 0 hi (by omega) (by omega) b
  · simp only [arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput,
      arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion, Category.assoc,
      arithmeticLastRetainedMixedZeroBoundaryOutput_base, pullbackSymmetry_inv_comp_fst_assoc]
    rw [pullback.condition]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
