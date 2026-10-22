/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentSelfFlexibleTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticTargetFlexiblePreMiddle
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMixedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Flexible near-terminal adjacent retained sources

The unshifted sum/reflected formulas, punctured self transfer, and full mixed
last transfer retain their genuine stage bounds. This includes feasible
incomplete terminal resolutions beyond the two exact boundary depths.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticFixedAdjacentSourceCoordinates
  arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i : ℕ) (hk : i + 3 ≤ n) (hdepth : 2 * (i + 3) < depth)
  (hnear : depth ≤ (i + 1) + 2 * (i + 3))
  (hsum : min (2 * i + 3) (depth - (2 * i + 3)) ≤ i + 3)
  (hself : min (2 * (i + 2)) (depth - 2 * (i + 2)) ≤ i + 3)
local notation "j" => i + 1
local notation "k" => i + 3
local notation "hi" => (by omega : i + 2 ≤ k)
local notation "hj" => (by omega : j + 2 ≤ k)
local notation "hiNext" => (by omega : (i + 1) + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le ((hi).trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le ((hj).trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticTargetFlexiblePreMiddleChart node data m k hk i j hi hj
  (by omega) (by omega) (by omega)
local notation "SC" => arithmeticRetainedAdjacentSelfFlexibleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "SO" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "MC" => arithmeticLastRetainedMixedBoundaryChart node data m (j + 1) hk
  (i + 1) (by omega) (by omega) (by omega)
local notation "MO" => arithmeticLastRetainedMixedBoundaryOutput node data m (j + 1) hk
  (i + 1) (by omega) (by omega) (by omega)
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticLastRetainedPairOpen node data m (j + 1) hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Three unshifted, two earlier-transfer, and six last-transfer domains. -/
abbrev LastRetainedAdjacentFlexibleLocalIndex :=
  Fin 3 ⊕ (Bool ⊕ MixedBoundaryNodalLocalIndex)

/-- Actual open domains inside the original pair or its incidence source. -/
def arithmeticLastRetainedAdjacentFlexibleLocalSource :
    LastRetainedAdjacentFlexibleLocalIndex → Scheme
  | .inl b => (V b).toScheme
  | .inr (.inl b) => (SC b).toScheme
  | .inr (.inr b) => (MC b).toScheme

local notation "X" => arithmeticLastRetainedAdjacentFlexibleLocalSource
  node data m i hk hdepth hnear hsum hself

/-- Each source embeds into the complete original ordered pair. -/
def arithmeticLastRetainedAdjacentFlexibleLocalInclusion :
    (b : LastRetainedAdjacentFlexibleLocalIndex) → X b ⟶ pullback f g
  | .inl b => (V b).ι
  | .inr (.inl b) => (SC b).ι ≫ (S).ι
  | .inr (.inr b) => (MC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv

local notation "inc" => arithmeticLastRetainedAdjacentFlexibleLocalInclusion
  node data m i hk hdepth hnear hsum hself

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedAdjacentFlexibleLocalInclusion_open
    (b : LastRetainedAdjacentFlexibleLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with b | (b | b) <;>
    dsimp only [arithmeticLastRetainedAdjacentFlexibleLocalInclusion] <;> infer_instance

/-- All sources carry whole arithmetic quotient outputs. -/
def arithmeticLastRetainedAdjacentFlexibleLocalOutput :
    (b : LastRetainedAdjacentFlexibleLocalIndex) → X b ⟶ pullback q t
  | .inl b => arithmeticTargetFlexiblePreMiddleOutput
      node data m k hk i j hi hj (by omega) (by omega) (by omega) b
  | .inr (.inl b) => SO b
  | .inr (.inr b) => MO b

/-- The output retains the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentFlexibleLocalOutput_base
    (b : LastRetainedAdjacentFlexibleLocalIndex) :
    arithmeticLastRetainedAdjacentFlexibleLocalOutput
      node data m i hk hdepth hnear hsum hself b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with b | (b | b)
  · exact arithmeticTargetFlexiblePreMiddleOutput_base
      node data m k hk i j hi hj (by omega) (by omega) (by omega) b
  · dsimp only [arithmeticLastRetainedAdjacentFlexibleLocalOutput,
      arithmeticLastRetainedAdjacentFlexibleLocalInclusion]
    have hb := arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base
      node data m k hk (i + 1) hiNext (by omega) (by omega) b
    exact hb
  · simp only [arithmeticLastRetainedAdjacentFlexibleLocalOutput,
      arithmeticLastRetainedAdjacentFlexibleLocalInclusion, Category.assoc,
      arithmeticLastRetainedMixedBoundaryOutput_base, pullbackSymmetry_inv_comp_fst_assoc]
    rw [pullback.condition]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
