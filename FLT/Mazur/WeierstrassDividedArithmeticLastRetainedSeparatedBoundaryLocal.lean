/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSingleFlexiblePreMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMixedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Full local outputs for separated last-retained boundary pairs

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
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i j : ℕ) (hk : j + 2 ≤ n) (hgap : i + 1 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hnear : depth ≤ (i + 1) + 2 * (j + 2))
  (hstage : max (min (i + j + 2) (depth - (i + j + 2)))
    (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2)
local notation "k" => j + 2
local notation "hi" => (by omega : i + 2 ≤ k)
local notation "hj" => (by omega : j + 2 ≤ k)
local notation "hiNext" => (by omega : (i + 1) + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
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
local notation "SC" => arithmeticRetainedSingleFlexiblePreMiddleChart node data m k hk
  (i + 1) j hiNext hj (by omega) (by omega) (by omega)
local notation "SO" => arithmeticRetainedSingleFlexiblePreMiddleOutput node data m k hk
  (i + 1) j hiNext hj (by omega) (by omega) (by omega)
local notation "MC" => arithmeticLastRetainedMixedBoundaryChart node data m (j + 1) hk
  (i + 1) (by omega) hdepth hnear
local notation "MO" => arithmeticLastRetainedMixedBoundaryOutput node data m (j + 1) hk
  (i + 1) (by omega) hdepth hnear
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticLastRetainedPairOpen node data m (j + 1) hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Three unshifted, three earlier-transfer, and six last-transfer domains. -/
abbrev LastRetainedSeparatedBoundaryLocalIndex := Sum (Bool × Fin 3) MixedBoundaryNodalLocalIndex

/-- Actual open domains inside the original pair or its incidence source. -/
def arithmeticLastRetainedSeparatedBoundaryLocalSource :
    LastRetainedSeparatedBoundaryLocalIndex → Scheme
  | .inl (false, b) => (V b).toScheme
  | .inl (true, b) => (SC b).toScheme
  | .inr b => (MC b).toScheme

local notation "X" => arithmeticLastRetainedSeparatedBoundaryLocalSource
  node data m i j hk hgap hdepth hnear hstage

/-- Each source embeds into the complete original ordered pair. -/
def arithmeticLastRetainedSeparatedBoundaryLocalInclusion :
    (b : LastRetainedSeparatedBoundaryLocalIndex) → X b ⟶ pullback f g
  | .inl (false, b) => (V b).ι
  | .inl (true, b) => (SC b).ι ≫ (S).ι
  | .inr b => (MC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv

local notation "inc" => arithmeticLastRetainedSeparatedBoundaryLocalInclusion
  node data m i j hk hgap hdepth hnear hstage

/-- Every formula source is a genuine open subchart of the original pair. -/
instance arithmeticLastRetainedSeparatedBoundaryLocalInclusion_open
    (b : LastRetainedSeparatedBoundaryLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with ⟨a, b⟩ | b
  · cases a <;> dsimp only [arithmeticLastRetainedSeparatedBoundaryLocalInclusion] <;>
      infer_instance
  · dsimp only [arithmeticLastRetainedSeparatedBoundaryLocalInclusion]
    infer_instance

/-- All sources carry whole arithmetic quotient outputs. -/
def arithmeticLastRetainedSeparatedBoundaryLocalOutput :
    (b : LastRetainedSeparatedBoundaryLocalIndex) → X b ⟶ pullback q t
  | .inl (false, b) => arithmeticTargetFlexiblePreMiddleOutput
      node data m k hk i j hi hj (by omega) (by omega) (by omega) b
  | .inl (true, b) => SO b
  | .inr b => MO b

/-- The output retains the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundaryLocalOutput_base
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedSeparatedBoundaryLocalOutput
      node data m i j hk hgap hdepth hnear hstage b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with ⟨a, b⟩ | b
  · cases a <;>
      simp only [arithmeticLastRetainedSeparatedBoundaryLocalOutput,
        arithmeticLastRetainedSeparatedBoundaryLocalInclusion, Category.assoc,
        arithmeticTargetFlexiblePreMiddleOutput_base,
        arithmeticRetainedSingleFlexiblePreMiddleOutput_base]
  · simp only [arithmeticLastRetainedSeparatedBoundaryLocalOutput,
      arithmeticLastRetainedSeparatedBoundaryLocalInclusion, Category.assoc,
      arithmeticLastRetainedMixedBoundaryOutput_base, pullbackSymmetry_inv_comp_fst_assoc]
    rw [pullback.condition]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
