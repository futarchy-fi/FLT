/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedOddLocal

/-!
# Actual local sources for the odd last-retained/terminal pair

Join the three unshifted normalized domains with both terminal incidence
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
variable (hodd : depth = 2 * (j + 1) + 1) (hj0 : 0 < j)
local notation "E" => arithmeticMixedNodalReflectedChart node data m (j + 1) hj
  j (Nat.lt_succ_self j) (by omega) (by omega)
local notation "C" => arithmeticLastRetainedOddIncidenceChart node data m j hj hodd

local notation "X" => arithmeticLastRetainedOddLocalSource node data m j hj hodd hj0
local notation "J" => arithmeticLastRetainedOddLocalInclusion node data m j hj hodd hj0
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

local instance arithmeticLastRetainedOddLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The five genuine sources cover every original smooth last-retained/odd-terminal pair. -/
theorem arithmeticLastRetainedOddLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f g' : Scheme))
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
    exact ⟨.inr b, ⟨w, hb⟩, rfl⟩
  · obtain ⟨v, hv⟩ := arithmeticSmoothPairInclusion_exists
      hπ data m (j + 1) hj a 1 p hs ht
    have he : (A a).ι (pullback.fst fa fb v) = pullback.fst f g' p := by
      rw [← hv]
      exact congrArg (fun morphism => morphism v)
        (arithmeticSmoothPairInclusion_first hπ data m (j + 1) hj a 1).symm
    obtain ⟨c, hc⟩ := arithmeticMixedNodalReflectedChart_tensor
      node data m (j + 1) hj j (Nat.lt_succ_self j)
      (by omega) (by omega) hj0 (by omega) v (by
        erw [← arithmeticLastRetainedIndexedCoordinates, he]
        exact hx)
    exact ⟨.inl c, ⟨v, hc⟩, hv⟩

/-- The genuine source images exhaust the full original smooth-pair open. -/
theorem arithmeticLastRetainedOddLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f g' ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g' ≫ chart 1) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ c, (J c).opensRange := by
  intro p hp
  obtain ⟨c, z, hz⟩ := arithmeticLastRetainedOddLocal_exists
    node data m j hj hodd hj0 hgen p hp.1 hp.2
  exact (le_iSup (fun c => (J c).opensRange) c) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
