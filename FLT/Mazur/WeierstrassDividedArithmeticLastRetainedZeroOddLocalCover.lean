/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroOddLocal

/-!
# Actual local sources for the creation-zero odd boundary pair

Join the unshifted difference domain with both terminal incidence
sources. Each embeds openly in the original pair and retains its quotient output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticTensorAtlasMap globalTensorAtlasObject
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


local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "fa" => (A a).ι ≫ chart a ≫ s
local notation "fb" => (A 1).ι ≫ chart 1 ≫ s
local notation "I" => arithmeticSmoothPairInclusion hπ data m (j + 1) hj a 1
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "D" => arithmeticLastRetainedMiddleSmoothOpen node data m j hj
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (hodd : depth = 2 * (j + 1) + 1)
local notation "V" => arithmeticRetainedTerminalOpen hπ data m (j + 1) hj
  j (j + 1) (Nat.lt_succ_self j) le_rfl (Nat.le_succ j)
local notation "C" => arithmeticLastRetainedOddIncidenceChart node data m j hj hodd

local notation "X" => arithmeticLastRetainedZeroOddLocalSource node data m j hj hodd
local notation "J" => arithmeticLastRetainedZeroOddLocalInclusion node data m j hj hodd
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

local instance arithmeticLastRetainedZeroOddLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The three genuine sources cover every original smooth last-retained/odd-terminal pair. -/
theorem arithmeticLastRetainedZeroOddLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0) (p : (pullback f g' : Scheme))
    (hs : chart a (pullback.fst f g' p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g' p) ∈ (s).smoothLocus) :
    ∃ c, ∃ z : X c, J c z = p := by
  classical
  by_cases hx : u ∈ (coords (pullback.fst f g' p)).asIdeal
  · let v : (O).toScheme := ⟨p, arithmeticLastRetainedPairOpen_zero_mem
      node data m j hj g' hgen (by omega) p hs hx⟩
    let w : (D).toScheme := ⟨v, by
      constructor
      · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj a _).mpr hs
      · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj 1 _).mpr ht⟩
    have hw : w ∈ (⨆ b, C b) := by
      rw [arithmeticLastRetainedOddIncidenceChart_covers]
      trivial
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
    exact ⟨some b, ⟨w, hb⟩, rfl⟩
  · obtain ⟨v, hv⟩ := arithmeticSmoothPairInclusion_exists
      hπ data m (j + 1) hj a 1 p hs ht
    have he : (A a).ι (pullback.fst fa fb v) = pullback.fst f g' p := by
      rw [← hv]
      exact congrArg (fun morphism => morphism v)
        (arithmeticSmoothPairInclusion_first hπ data m (j + 1) hj a 1).symm
    have hvV : v ∈ V := by
      apply arithmeticMixed_zero_horizontal_le_middle_mem hπ data m (j + 1) hj j
        (Nat.lt_succ_self j) node hzero (by omega) v
      erw [← arithmeticLastRetainedIndexedCoordinates, he]
      exact hx
    exact ⟨none, ⟨v, hvV⟩, hv⟩

/-- The genuine source images exhaust the full original smooth-pair open. -/
theorem arithmeticLastRetainedZeroOddLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0) :
    (pullback.fst f g' ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g' ≫ chart 1) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ c, (J c).opensRange := by
  intro p hp
  obtain ⟨c, z, hz⟩ := arithmeticLastRetainedZeroOddLocal_exists
    node data m j hj hodd hgen hzero p hp.1 hp.2
  exact (le_iSup (fun c => (J c).opensRange) c) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
