/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSingleFlexiblePreMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMixedZeroBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticSourceTargetZeroAddition

/-!
# Full local outputs for creation-zero/last-retained boundary pairs

Combine unshifted formulas, the earlier adjacent transfer, and the complete
last-transfer incidence cover. The latter also contains the double-zero case.
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
  (m j : ℕ) (hk : j + 2 ≤ n) (hj0 : 0 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hnear : depth ≤ 1 + 2 * (j + 2))
local notation "k" => j + 2
local notation "hi" => (Nat.le_add_left 2 j)
local notation "hj" => (Nat.le_refl (j + 2))
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨1, Nat.lt_succ_of_le ((Nat.le_trans
  (Nat.le_succ 1) hi).trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le hk⟩
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk 0 hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "u" => tensorCoord W (π ^ (0 + 0)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticSourceTargetOppositeOpen node data m k hk 0 j hi hj
  (by omega) (by omega)
local notation "SC" => arithmeticRetainedSingleFlexiblePreMiddleChart node data m k hk
  0 j hi hj (by omega) (by omega) (by omega)
local notation "SO" => arithmeticRetainedSingleFlexiblePreMiddleOutput node data m k hk
  0 j hi hj (by omega) (by omega) (by omega)
local notation "MC" => arithmeticLastRetainedMixedZeroBoundaryChart node data m (j + 1) hk
  0 (by omega) hdepth hnear
local notation "MO" => arithmeticLastRetainedMixedZeroBoundaryOutput node data m (j + 1) hk
  0 (by omega) hdepth hnear
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk 0 hi g
local notation "T" => arithmeticLastRetainedPairOpen node data m (j + 1) hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- One unshifted domain, three earlier-transfer domains, and the last-transfer sources. -/
abbrev LastRetainedZeroSeparatedBoundaryLocalIndex :=
  Unit ⊕ (Fin 3 ⊕ MixedZeroBoundaryNodalLocalIndex)

/-- Actual open domains inside the original pair or its incidence source. -/
def arithmeticLastRetainedZeroSeparatedBoundaryLocalSource :
    LastRetainedZeroSeparatedBoundaryLocalIndex → Scheme
  | .inl _ => (V).toScheme
  | .inr (.inl b) => (SC b).toScheme
  | .inr (.inr b) => (MC b).toScheme

local notation "X" => arithmeticLastRetainedZeroSeparatedBoundaryLocalSource
  node data m j hk hj0 hdepth hnear

/-- Each source embeds into the complete original ordered pair. -/
def arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion :
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) → X b ⟶ pullback f g
  | .inl _ => (V).ι
  | .inr (.inl b) => (SC b).ι ≫ (S).ι
  | .inr (.inr b) => (MC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv

local notation "inc" => arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion
  node data m j hk hj0 hdepth hnear

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion_open
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with b | (b | b) <;>
    dsimp only [arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion] <;> infer_instance

/-- All sources carry whole arithmetic quotient outputs. -/
def arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput :
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) → X b ⟶ pullback q t
  | .inl _ => arithmeticSourceTargetOppositeQuotientOutput
      node data m k hk 0 j hi hj (by omega) (by omega)
  | .inr (.inl b) => SO b
  | .inr (.inr b) => MO b

/-- The output retains the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput_base
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput
      node data m j hk hj0 hdepth hnear b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with b | (b | b)
  · exact arithmeticSourceTargetOppositeQuotientOutput_base
      node data m k hk 0 j hi hj (by omega) (by omega)
  · simpa only [arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput,
      arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion, Category.assoc] using
      arithmeticRetainedSingleFlexiblePreMiddleOutput_base
        node data m k hk 0 j hi hj (by omega) (by omega) (by omega) b
  · simp only [arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput,
      arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion, Category.assoc,
      arithmeticLastRetainedMixedZeroBoundaryOutput_base, pullbackSymmetry_inv_comp_fst_assoc]
    rw [pullback.condition]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
