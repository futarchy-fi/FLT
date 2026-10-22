/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedIndexed

/-!
# Indexed terminal transfer with an arbitrary second input

The final retained chart moves to the terminal chart on its actual incidence
open. Both full input morphisms are preserved, at every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
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
variable {Y : Scheme}
  (g : Y ⟶ Spec (.of (Quotient R π m)))

/-- Reindex the first input while retaining any second input over the quotient. -/
def arithmeticLastRetainedPairReindex : pullback f g ⟶ pullback f₀ g :=
  pullback.lift (pullback.fst f g ≫ coords) (pullback.snd f g) (by
    rw [Category.assoc, arithmeticLastRetainedIndexed_chart_assoc]
    exact pullback.condition)

local notation "reindex" => arithmeticLastRetainedPairReindex node data m j hj g

omit [IsNoetherianRing R] in
/-- Reindexing preserves the first complete tensor coordinate. -/
@[reassoc] theorem arithmeticLastRetainedPairReindex_first :
    reindex ≫ pullback.fst f₀ g = pullback.fst f g ≫ coords :=
  pullback.lift_fst _ _ _

omit [IsNoetherianRing R] in
/-- Reindexing leaves the arbitrary second input unchanged. -/
@[reassoc] theorem arithmeticLastRetainedPairReindex_second :
    reindex ≫ pullback.snd f₀ g = pullback.snd f g := pullback.lift_snd _ _ _

attribute [irreducible] arithmeticLastRetainedPairReindex

omit [IsNoetherianRing R] in
/-- The reindexed pair has precisely the original complete first coordinate point. -/
theorem arithmeticLastRetainedPairReindex_point (p : (pullback f g : Scheme)) :
    pullback.fst f₀ g (reindex p) = coords (pullback.fst f g p) := by
  have h := congrArg (fun morphism => morphism p)
    (arithmeticLastRetainedPairReindex_first node data m j hj g)
  simpa only [Scheme.Hom.comp_apply] using h

omit [IsNoetherianRing R] in
/-- The reindexed first coordinate represents the original resolved arithmetic point. -/
theorem arithmeticLastRetainedPairReindex_chart_point (p : (pullback f g : Scheme)) :
    old (pullback.fst f₀ g (reindex p)) = chart a (pullback.fst f g p) := by
  rw [arithmeticLastRetainedPairReindex_point]
  have h := congrArg (fun morphism => morphism (pullback.fst f g p))
    (arithmeticLastRetainedIndexed_chart node data m j hj)
  simpa only [Scheme.Hom.comp_apply] using h

local notation "V" => arithmeticTerminalPairOpen hπ data m j hj g

/-- The indexed incidence domain is the preimage of the native terminal boundary. -/
def arithmeticLastRetainedPairOpen : (pullback f g).Opens := reindex ⁻¹ᵁ V

local notation "D" => arithmeticLastRetainedPairOpen node data m j hj g

/-- Transfer to the actual indexed terminal chart, retaining the entire second input. -/
def arithmeticLastRetainedPairTransfer : (D).toScheme ⟶ pullback g' g :=
  (reindex ∣_ V) ≫ arithmeticTerminalPairTransfer hπ data m j hj g ≫
    pullback.lift (pullback.fst f' g ≫ (E).hom) (pullback.snd f' g) (by
      simp only [Category.assoc, arithmeticTensorAtlas_terminal_assoc]
      exact pullback.condition)

local notation "transfer" => arithmeticLastRetainedPairTransfer node data m j hj g

omit [IsNoetherianRing R] in
/-- The transferred first input equals the full original resolved arithmetic input. -/
@[reassoc] theorem arithmeticLastRetainedPairTransfer_first :
    transfer ≫ pullback.fst g' g ≫ chart 1 = (D).ι ≫ pullback.fst f g ≫ chart a := by
  dsimp only [arithmeticLastRetainedPairOpen]
  simp only [arithmeticLastRetainedPairTransfer, Category.assoc, pullback.lift_fst_assoc,
    arithmeticTensorAtlas_terminal, arithmeticTerminalPairTransfer_first]
  rw [morphismRestrict_ι_assoc]
  rw [arithmeticLastRetainedPairReindex_first_assoc,
    arithmeticLastRetainedIndexed_chart]

omit [IsNoetherianRing R] in
/-- The transfer leaves all functions of the second input unchanged. -/
@[reassoc] theorem arithmeticLastRetainedPairTransfer_second :
    transfer ≫ pullback.snd g' g = (D).ι ≫ pullback.snd f g := by
  dsimp only [arithmeticLastRetainedPairOpen]
  simp only [arithmeticLastRetainedPairTransfer, Category.assoc, pullback.lift_snd,
    arithmeticTerminalPairTransfer_second]
  rw [morphismRestrict_ι_assoc]
  rw [arithmeticLastRetainedPairReindex_second]

local instance arithmeticLastRetainedPair_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

/-- Every smooth horizontal-zero input belongs to this whole incidence domain. -/
theorem arithmeticLastRetainedPairOpen_zero_mem
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hm : 2 * (j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g p)).asIdeal) : p ∈ D := by
  change reindex p ∈ V
  have hs' := hs
  rw [← arithmeticLastRetainedPairReindex_chart_point node data m j hj g p] at hs'
  have hx' := hx
  rw [← arithmeticLastRetainedPairReindex_point node data m j hj g p] at hx'
  exact arithmeticTerminalPairOpen_anyDepth_zero_mem hπ data node hgen m j hj g
    (by omega) (reindex p) hs' hx'

end FLT.Mazur.WeierstrassDividedDepth
