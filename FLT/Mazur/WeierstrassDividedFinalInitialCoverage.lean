/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialComponentRanges
public import FLT.Mazur.WeierstrassDividedFinalInitialComponents
public import FLT.Mazur.WeierstrassDividedFinalChainCoverage

/-!
# Initial components cover the initial conic and first retained lines

The original complete component maps are transported to the fixed final stage.
The first retained chart is covered by its conic and these two initial components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Index transport preserves the entire original initial conic. -/
@[reassoc] theorem initialGlobalConic_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (hstart : 0 < start) (hk : 2 * start ≤ depth) :
    initialGlobalConic hπ data D a ha hstart hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      initialGlobalConic hπ data D b hb hstart hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := 1 + s) (b := s + 1) (by omega) hs (by omega))

/-- The full initial conic is contained in the two fixed-stage initial component images. -/
theorem finalInitialComponents_cover_conic :
    Set.range (initialGlobalConic hπ data D (s + 1) hs hstart (by omega)) ⊆
      Set.range (finalInitialComponent hπ data D s hs hstart hk 0) ∪
        Set.range (finalInitialComponent hπ data D s hs hstart hk 1) := by
  let t := componentCoverageTransport (finiteGlobalTensorModel_index_congr hπ data K
    (a := 1 + s) (b := s + 1) (by omega) hs (by omega))
  exact componentRange_subset_transport
    (initialGlobalConic hπ data D (1 + s) (by omega) hstart (by omega))
    (initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega))
    (initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega)) t
    (initialGlobalConic hπ data D (s + 1) hs hstart (by omega))
    (finalInitialComponent hπ data D s hs hstart hk 0)
    (finalInitialComponent hπ data D s hs hstart hk 1)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact initialGlobalConic_index_transport hπ data D _ hs (by omega) hstart _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (initialGlobalComponents_cover_conic hπ data D (by omega) hstart (by omega) s (by omega))

/-- The first retained chart is covered by its conic and both original initial components. -/
theorem finalInitialComponents_cover_first_chart :
    Set.range (retainedTensorChartAt hπ data (s + 1) hs 0 (by omega)) ⊆
      Set.range (retainedConicAt hπ data D (s + 1) hs 0 (by omega) (by omega)) ∪
        (Set.range (finalInitialComponent hπ data D s hs hstart hk 0) ∪
        Set.range (finalInitialComponent hπ data D s hs hstart hk 1)) := by
  have H : Set.range (retainedTensorChartAt hπ data (1 + s) (by omega) 0 (by omega)) ⊆
      Set.range (retainedConicAt hπ data D (1 + s) (by omega) 0 (by omega) (by omega)) ∪
        (Set.range (initialGlobalFirstComponent hπ data D (by omega)
          hstart (by omega) s (by omega)) ∪
        Set.range (initialGlobalSecondComponent hπ data D (by omega)
          hstart (by omega) s (by omega))) := by
    rw [retainedTensorChartAt_original hπ data 0 (by omega) s (by omega),
      retainedConicAt_original hπ data D 0 (by omega) s (by omega),
      orderedRetainedConic_positive hπ data D 0 (by omega) s (by omega) (by omega) hstart]
    intro x hx
    rw [← olderGlobalMiddleComponents_cover hπ data D 0 (by omega) s (by omega)
      hstart (by omega)] at hx
    rcases hx with hc | hl
    · exact Or.inl hc
    · exact Or.inr ((initialGlobalComponents_conic_range hπ data D (by omega)
        hstart (by omega) s (by omega)).symm ▸ Or.inr hl)
  let t := componentCoverageTransport (finiteGlobalTensorModel_index_congr hπ data K
    (a := 1 + s) (b := s + 1) (by omega) hs (by omega))
  exact componentRange_triple_subset_transport
    (retainedTensorChartAt hπ data (1 + s) (by omega) 0 (by omega))
    (retainedConicAt hπ data D (1 + s) (by omega) 0 (by omega) (by omega))
    (initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega))
    (initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega)) t
    (retainedTensorChartAt hπ data (s + 1) hs 0 (by omega))
    (retainedConicAt hπ data D (s + 1) hs 0 (by omega) (by omega))
    (finalInitialComponent hπ data D s hs hstart hk 0)
    (finalInitialComponent hπ data D s hs hstart hk 1)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedTensorChartAt_index_transport hπ data _ hs (by omega) _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedConicAt_index_transport hπ data D _ hs (by omega) _ _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl) H

end FLT.Mazur.WeierstrassDividedDepth
