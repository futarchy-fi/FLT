/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOrderedPairCoverage

/-!
# Full retained charts in the fixed branch-chain component images

Index transport preserves the conic containment and the coverage of each next
middle chart by its conic and the preceding pair of projective components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Postcomposition preserves coverage by two complete component maps. -/
theorem componentRange_subset_postcomp {A B C X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (t : X ⟶ Y)
    (he : Set.range f ⊆ Set.range g ∪ Set.range h) :
    Set.range (f ≫ t) ⊆ Set.range (g ≫ t) ∪ Set.range (h ≫ t) := by
  rintro _ ⟨x, rfl⟩
  rcases he ⟨x, rfl⟩ with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, congrArg t hy⟩
  · exact Or.inr ⟨y, congrArg t hy⟩

/-- Postcomposition preserves coverage by a conic and two component maps. -/
theorem componentRange_triple_subset_postcomp {A B C E X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (e : E ⟶ X) (t : X ⟶ Y)
    (he : Set.range f ⊆ Set.range g ∪ (Set.range h ∪ Set.range e)) :
    Set.range (f ≫ t) ⊆ Set.range (g ≫ t) ∪
      (Set.range (h ≫ t) ∪ Set.range (e ≫ t)) := by
  rintro _ ⟨x, rfl⟩
  rcases he ⟨x, rfl⟩ with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, congrArg t hy⟩
  · exact Or.inr (Or.inl ⟨y, congrArg t hy⟩)
  · exact Or.inr (Or.inr ⟨y, congrArg t hy⟩)

/-- A two-map cover transports along specified equalities of the complete scheme maps. -/
theorem componentRange_subset_transport {A B C X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (t : X ⟶ Y)
    (f' : A ⟶ Y) (g' : B ⟶ Y) (h' : C ⟶ Y)
    (hf : f ≫ t = f') (hg : g ≫ t = g') (hh : h ≫ t = h')
    (he : Set.range f ⊆ Set.range g ∪ Set.range h) :
    Set.range f' ⊆ Set.range g' ∪ Set.range h' := by
  rw [← hf, ← hg, ← hh]
  exact componentRange_subset_postcomp f g h t he

/-- A three-map cover transports along equalities of the complete scheme maps. -/
theorem componentRange_triple_subset_transport {A B C E X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (e : E ⟶ X) (t : X ⟶ Y)
    (f' : A ⟶ Y) (g' : B ⟶ Y) (h' : C ⟶ Y) (e' : E ⟶ Y)
    (hf : f ≫ t = f') (hg : g ≫ t = g') (hh : h ≫ t = h') (he : e ≫ t = e')
    (H : Set.range f ⊆ Set.range g ∪ (Set.range h ∪ Set.range e)) :
    Set.range f' ⊆ Set.range g' ∪ (Set.range h' ∪ Set.range e') := by
  rw [← hf, ← hg, ← hh, ← he]
  exact componentRange_triple_subset_postcomp f g h e t H

/-- A sealed scheme equality transport keeps heavy model definitions out of range reductions. -/
irreducible_def componentCoverageTransport {X Y : Scheme.{u}} (he : X = Y) : X ⟶ Y :=
  eqToHom he

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Equality of target stage indices preserves the complete original retained chart. -/
@[reassoc] theorem retainedTensorChartAt_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) (j : ℕ) (hj : j + 1 ≤ a) :
    retainedTensorChartAt hπ data a ha j hj ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      retainedTensorChartAt hπ data b hb j (by omega) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- Each full retained conic is contained in the corresponding adjacent pair. -/
theorem finalAdjacentComponents_cover_conic (j : Fin s) :
    Set.range (retainedConicAt hπ data D (s + 1) hs j.val (by omega) (by omega)) ⊆
      Set.range (finalAdjacentComponent hπ data D s hs hk j 0) ∪
        Set.range (finalAdjacentComponent hπ data D s hs hk j 1) := by
  let r := s - (j.val + 1)
  let t := componentCoverageTransport (finiteGlobalTensorModel_index_congr hπ data K
    (a := j.val + 2 + r) (b := s + 1) (by dsimp [r]; omega) hs (by dsimp [r]; omega))
  have H := orderedAdjacentComponents_cover_conic hπ data D j.val (by omega) (by omega)
    r (by dsimp [r]; omega) (by omega) (by omega)
  exact componentRange_subset_transport
    (retainedConicAt hπ data D (j.val + 2 + r)
      (by dsimp [r]; omega) j.val (by omega) (by omega))
    (orderedAdjacentComponent hπ data D j.val (by omega) (by omega)
      (by omega) (by omega) r (by dsimp [r]; omega) 0)
    (orderedAdjacentComponent hπ data D j.val (by omega) (by omega)
      (by omega) (by omega) r (by dsimp [r]; omega) 1) t
    (retainedConicAt hπ data D (s + 1) hs j.val (by omega) (by omega))
    (finalAdjacentComponent hπ data D s hs hk j 0)
    (finalAdjacentComponent hπ data D s hs hk j 1)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedConicAt_index_transport hπ data D _ hs (by dsimp [r]; omega) _ _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl) H

/-- Each next full middle chart lies in its conic and the preceding adjacent pair. -/
theorem finalAdjacentComponents_cover_next_chart (j : Fin s) :
    Set.range (retainedTensorChartAt hπ data (s + 1) hs (j.val + 1) (by omega)) ⊆
      Set.range (retainedConicAt hπ data D (s + 1) hs (j.val + 1) (by omega) (by omega)) ∪
        (Set.range (finalAdjacentComponent hπ data D s hs hk j 0) ∪
        Set.range (finalAdjacentComponent hπ data D s hs hk j 1)) := by
  let r := s - (j.val + 1)
  let t := componentCoverageTransport (finiteGlobalTensorModel_index_congr hπ data K
    (a := j.val + 2 + r) (b := s + 1) (by dsimp [r]; omega) hs (by dsimp [r]; omega))
  have H := orderedAdjacentComponents_cover_next_chart hπ data D j.val (by omega) (by omega)
    r (by dsimp [r]; omega) (by omega) (by omega)
  exact componentRange_triple_subset_transport
    (retainedTensorChartAt hπ data (j.val + 2 + r)
      (by dsimp [r]; omega) (j.val + 1) (by omega))
    (retainedConicAt hπ data D (j.val + 2 + r)
      (by dsimp [r]; omega) (j.val + 1) (by omega) (by omega))
    (orderedAdjacentComponent hπ data D j.val (by omega) (by omega)
      (by omega) (by omega) r (by dsimp [r]; omega) 0)
    (orderedAdjacentComponent hπ data D j.val (by omega) (by omega)
      (by omega) (by omega) r (by dsimp [r]; omega) 1) t
    (retainedTensorChartAt hπ data (s + 1) hs (j.val + 1) (by omega))
    (retainedConicAt hπ data D (s + 1) hs (j.val + 1) (by omega) (by omega))
    (finalAdjacentComponent hπ data D s hs hk j 0)
    (finalAdjacentComponent hπ data D s hs hk j 1)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedTensorChartAt_index_transport hπ data _ hs (by dsimp [r]; omega) _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]
        exact retainedConicAt_index_transport hπ data D _ hs (by dsimp [r]; omega) _ _ _)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl)
    (by dsimp only [t]; rw [componentCoverageTransport_def]; rfl) H

variable (hp : 2 * (start + s + 1) < depth)

/-- Every full retained conic lies in its actual pair of complete chain components. -/
theorem finalBranchComponents_cover_conic (j : Fin (s + 1)) :
    Set.range (retainedConicAt hπ data D (s + 1) hs j.val (by omega) (by omega)) ⊆
      Set.range (finalBranchComponent hπ data D s hs hk hp j 0).left ∪
        Set.range (finalBranchComponent hπ data D s hs hk hp j 1).left := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h, finalBranchComponent, dite_eq_left h]
    exact finalAdjacentComponents_cover_conic hπ data D s hs hk ⟨j.val, h⟩
  · have he : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal, finalBranchComponent_terminal]
    exact Set.subset_union_left.trans
      (le_of_eq (finalTerminalComponents_conic_range hπ data D s hs hk hp).symm)

/-- The two last chain components contain the whole original terminal node chart. -/
theorem finalBranchComponents_cover_terminal :
    Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) ⊆
      Set.range (finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ 0).left ∪
        Set.range (finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ 1).left := by
  rw [finalBranchComponent_terminal, finalBranchComponent_terminal]
  exact Set.subset_union_right.trans
    (le_of_eq (finalTerminalComponents_conic_range hπ data D s hs hk hp).symm)

end FLT.Mazur.WeierstrassDividedDepth
