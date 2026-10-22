/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalAnyDepthCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfTriple
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfShallow
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth
public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates

/-!
# Indexed last-retained transfer to the full terminal self-product

Reindex the actual newest tensor chart before applying the incidence boundary.
The transferred smooth pair preserves the entire first resolved arithmetic
point and the entire second indexed terminal point, at every admissible depth.
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
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "I" => arithmeticRetainedTensorIso hπ data m (j + 1) hj j (Nat.lt_succ_self j)
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g" => chart 1 ≫ s
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj 1
local notation "fg" => (O).ι ≫ chart 1 ≫ s
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

/-- The inverse tensor indexing map with the actual indexed source type sealed. -/
def arithmeticLastRetainedIndexedCoordinates :
    globalTensorAtlasObject hπ data Q (j + 1) hj a ⟶
      Spec (.of (ScalarExtension W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q)) := (I).inv

local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj
attribute [irreducible] arithmeticLastRetainedIndexedCoordinates

omit [IsNoetherianRing R] in
/-- The inverse indexing map preserves the complete newest arithmetic chart morphism. -/
@[reassoc] theorem arithmeticLastRetainedIndexed_chart : coords ≫ old = chart a := by
  rw [arithmeticLastRetainedIndexedCoordinates,
    ← arithmeticRetainedTensorChart_newest hπ data j hj m]
  exact (I).inv_hom_id_assoc _

local instance arithmeticLastRetainedIndexed_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The native newest tensor pair transfers into the full smooth terminal self-product. -/
theorem arithmeticLastRetainedNative_terminal_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hdepth : 2 * (j + 1) ≤ depth)
    (p : (pullback f₀ g : Scheme))
    (hs : old (pullback.fst f₀ g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f₀ g p) ∈ (s).smoothLocus)
    (hx : u ∈ (pullback.fst f₀ g p).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = old (pullback.fst f₀ g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f₀ g p := by
  obtain ⟨q, hq, he, _⟩ := arithmeticTerminalPair_anyDepth_zero_coordinates
    hπ data node hgen m j hj g (by omega) p hs hx
  let transfer : pullback f' g ⟶ pullback g g :=
    pullback.lift (pullback.fst f' g ≫ (E).hom) (pullback.snd f' g) (by
      simp only [Category.assoc, arithmeticTensorAtlas_terminal_assoc]
      exact pullback.condition)
  have hf : transfer ≫ pullback.fst g g ≫ chart 1 = pullback.fst f' g ≫ next := by
    simp only [transfer, pullback.lift_fst_assoc, Category.assoc,
      arithmeticTensorAtlas_terminal]
  have hg : transfer ≫ pullback.snd g g = pullback.snd f' g := by
    simp only [transfer, pullback.lift_snd]
  have hfirst : chart 1 (pullback.fst g g (transfer q)) = old (pullback.fst f₀ g p) :=
    (congrArg (fun morphism => morphism q) hf).trans hq
  have hsecond : pullback.snd g g (transfer q) = pullback.snd f₀ g p :=
    (congrArg (fun morphism => morphism q) hg).trans he
  obtain ⟨z, hz, ht'⟩ := arithmeticAtlasRelativePair_exists hπ data m (j + 1) hj 1 1
    (transfer q) (by rw [hfirst]; exact hs) (by rw [hsecond]; exact ht)
  exact ⟨z, (congrArg (chart 1) hz).trans hfirst, ht'.trans hsecond⟩

/-- Reindex the full pair before moving its first input along the incidence boundary. -/
def arithmeticLastRetainedIndexedReindex : pullback f g ⟶ pullback f₀ g :=
  pullback.lift (pullback.fst f g ≫ coords) (pullback.snd f g) (by
    rw [Category.assoc, arithmeticLastRetainedIndexed_chart_assoc node data m j hj]
    exact pullback.condition)

local notation "reindex" => arithmeticLastRetainedIndexedReindex node data m j hj

omit [IsNoetherianRing R] in
/-- Reindexing retains the complete first tensor coordinate. -/
@[reassoc] theorem arithmeticLastRetainedIndexedReindex_first :
    reindex ≫ pullback.fst f₀ g = pullback.fst f g ≫ coords :=
  pullback.lift_fst _ _ _

omit [IsNoetherianRing R] in
/-- Reindexing leaves the second indexed terminal input unchanged. -/
@[reassoc] theorem arithmeticLastRetainedIndexedReindex_second :
    reindex ≫ pullback.snd f₀ g = pullback.snd f g := pullback.lift_snd _ _ _

attribute [irreducible] arithmeticLastRetainedIndexedReindex

omit [IsNoetherianRing R] in
/-- Reindexing identifies the full first tensor point. -/
theorem arithmeticLastRetainedIndexedReindex_point (p : (pullback f g : Scheme)) :
    pullback.fst f₀ g (reindex p) = coords (pullback.fst f g p) := by
  have h := congrArg (fun morphism => morphism p)
    (arithmeticLastRetainedIndexedReindex_first node data m j hj)
  simpa only [Scheme.Hom.comp_apply] using h

omit [IsNoetherianRing R] in
/-- Reindexing preserves the full resolved first arithmetic point. -/
theorem arithmeticLastRetainedIndexedReindex_chart_point (p : (pullback f g : Scheme)) :
    old (pullback.fst f₀ g (reindex p)) = chart a (pullback.fst f g p) := by
  rw [arithmeticLastRetainedIndexedReindex_point]
  have h := congrArg (fun morphism => morphism (pullback.fst f g p))
    (arithmeticLastRetainedIndexed_chart node data m j hj)
  simpa only [Scheme.Hom.comp_apply] using h

omit [IsNoetherianRing R] in
/-- The second indexed point is unchanged by reindexing. -/
theorem arithmeticLastRetainedIndexedReindex_second_point (p : (pullback f g : Scheme)) :
    pullback.snd f₀ g (reindex p) = pullback.snd f g p := by
  have h := congrArg (fun morphism => morphism p)
    (arithmeticLastRetainedIndexedReindex_second node data m j hj)
  simpa only [Scheme.Hom.comp_apply] using h

/-- The indexed nonpunctured pair transfers into the full smooth terminal self-product. -/
theorem arithmeticLastRetainedIndexed_terminal_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hdepth : 2 * (j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = chart a (pullback.fst f g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f g p := by
  have hr := arithmeticLastRetainedIndexedReindex_chart_point node data m j hj p
  have hsnd := arithmeticLastRetainedIndexedReindex_second_point node data m j hj p
  have hzero : u ∈ (pullback.fst f₀ g (reindex p)).asIdeal :=
    (arithmeticLastRetainedIndexedReindex_point node data m j hj p).symm ▸ hx
  obtain ⟨z, hz, he⟩ := arithmeticLastRetainedNative_terminal_target
    node data m j hj hgen hdepth (reindex p) (by rw [hr]; exact hs)
    (by rw [hsnd]; exact ht) hzero
  exact ⟨z, hz.trans hr, he.trans hsnd⟩

local notation "Drec" => arithmeticTerminalSelfReciprocalOpen hπ data m (j + 1) hj

/-- Indexed last-retained inputs reach the shallow or reciprocal output without a recast. -/
theorem arithmeticLastRetainedIndexed_shallow_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π)
    (hlo : 2 * (j + 1) < depth) (hhi : depth < 3 * (j + 1))
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = chart a (pullback.fst f g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f g p ∧
      (z ∈ arithmeticTerminalSelfShallowOpen node data m (j + 1) hj hlo hhi ∨ z ∈ Drec) := by
  obtain ⟨z, hz, he⟩ := arithmeticLastRetainedIndexed_terminal_target
    node data m j hj hgen hlo.le p hs ht hx
  exact ⟨z, hz, he,
    arithmeticTerminalSelfShallow_or_reciprocal_mem node data m (j + 1) hj hlo hhi z⟩

/-- Indexed last-retained inputs reach the intermediate or reciprocal output at triple depth. -/
theorem arithmeticLastRetainedIndexed_triple_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hdepth : depth = 3 * (j + 1))
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = chart a (pullback.fst f g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f g p ∧
      (z ∈ arithmeticTerminalSelfTripleOpen node data m (j + 1) hj hdepth ∨ z ∈ Drec) := by
  obtain ⟨z, hz, he⟩ := arithmeticLastRetainedIndexed_terminal_target
    node data m j hj hgen (by omega) p hs ht hx
  exact ⟨z, hz, he,
    arithmeticTerminalSelfTriple_or_reciprocal_mem node data m (j + 1) hj (by omega) hdepth z⟩

end FLT.Mazur.WeierstrassDividedDepth
