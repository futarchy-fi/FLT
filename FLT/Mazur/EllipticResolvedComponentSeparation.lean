/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentSupports

/-!
# Pairwise separation of the actual arithmetic component charts

Different depths lie in disjoint full boundaries. At the same depth the
positive and negative punctures are disjoint; parity excludes a middle
component at odd depth. These are geometric statements on the whole charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)

/-- Distinct arithmetic component indices have disjoint full original-fiber images. -/
theorem resolvedComponentCarriers_disjoint (i j : ResolvedComponentIndex depth) (hij : i ≠ j) :
    Disjoint (resolvedComponentCarrier A D r i) (resolvedComponentCarrier A D r j) := by
  cases i <;> cases j
  all_goals simp only [resolvedComponentCarrier]
  case identity.identity =>
    exact (hij rfl).elim
  case identity.retainedPositive b hb0 hb =>
    exact (resolvedRetainedPositiveChart_identity_disjoint A D r b hb0 hb).symm
  case identity.retainedNegative b hb0 hb =>
    exact (resolvedRetainedNegativeChart_identity_disjoint A D r b hb0 hb).symm
  case identity.terminalPositive hb0 hb =>
    exact ((resolvedTerminal_identity_disjoint A D hb0).mono_left
      (resolvedTerminalPositiveChart_subset_terminal A D r hb0 hb)).symm
  case identity.terminalNegative hb0 hb =>
    exact ((resolvedTerminal_identity_disjoint A D hb0).mono_left
      (resolvedTerminalNegativeChart_subset_terminal A D r hb0 hb)).symm
  case identity.terminalMiddle hb0 hb =>
    exact ((resolvedTerminal_identity_disjoint A D hb0).mono_left
      ((resolvedTerminalMiddleChart_range A D r hb0 hb).subset)).symm
  case retainedPositive.identity a ha0 ha =>
    exact resolvedRetainedPositiveChart_identity_disjoint A D r a ha0 ha
  case retainedPositive.retainedPositive a ha0 ha b hb0 hb =>
    have hab : a ≠ b := by
      intro he
      subst b
      exact hij rfl
    exact (resolvedRetainedBoundary_depth_disjoint A D a b ha hb hab).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r a ha0 ha)
      (resolvedRetainedPositiveChart_subset_boundary A D r b hb0 hb)
  case retainedPositive.retainedNegative a ha0 ha b hb0 hb =>
    by_cases he : a = b
    · subst b
      exact (resolvedRetainedCharts_disjoint A D r a ha0 ha).symm
    · exact (resolvedRetainedBoundary_depth_disjoint A D a b ha hb he).mono
        (resolvedRetainedPositiveChart_subset_boundary A D r a ha0 ha)
        (resolvedRetainedNegativeChart_subset_boundary A D r b hb0 hb)
  case retainedPositive.terminalPositive a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r a ha0 ha)
      (resolvedTerminalPositiveChart_subset_terminal A D r hb0 hb))
  case retainedPositive.terminalNegative a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r a ha0 ha)
      (resolvedTerminalNegativeChart_subset_terminal A D r hb0 hb))
  case retainedPositive.terminalMiddle a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r a ha0 ha)
      ((resolvedTerminalMiddleChart_range A D r hb0 hb).subset))
  case retainedNegative.identity a ha0 ha =>
    exact resolvedRetainedNegativeChart_identity_disjoint A D r a ha0 ha
  case retainedNegative.retainedPositive a ha0 ha b hb0 hb =>
    by_cases he : a = b
    · subst b
      exact (resolvedRetainedCharts_disjoint A D r a ha0 ha)
    · exact (resolvedRetainedBoundary_depth_disjoint A D a b ha hb he).mono
        (resolvedRetainedNegativeChart_subset_boundary A D r a ha0 ha)
        (resolvedRetainedPositiveChart_subset_boundary A D r b hb0 hb)
  case retainedNegative.retainedNegative a ha0 ha b hb0 hb =>
    have hab : a ≠ b := by
      intro he
      subst b
      exact hij rfl
    exact (resolvedRetainedBoundary_depth_disjoint A D a b ha hb hab).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r a ha0 ha)
      (resolvedRetainedNegativeChart_subset_boundary A D r b hb0 hb)
  case retainedNegative.terminalPositive a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r a ha0 ha)
      (resolvedTerminalPositiveChart_subset_terminal A D r hb0 hb))
  case retainedNegative.terminalNegative a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r a ha0 ha)
      (resolvedTerminalNegativeChart_subset_terminal A D r hb0 hb))
  case retainedNegative.terminalMiddle a ha0 ha hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D a ha).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r a ha0 ha)
      ((resolvedTerminalMiddleChart_range A D r hb0 hb).subset))
  case terminalPositive.identity ha0 ha =>
    exact ((resolvedTerminal_identity_disjoint A D ha0).mono_left
      (resolvedTerminalPositiveChart_subset_terminal A D r ha0 ha))
  case terminalPositive.retainedPositive ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r b hb0 hb)
      (resolvedTerminalPositiveChart_subset_terminal A D r ha0 ha)).symm
  case terminalPositive.retainedNegative ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r b hb0 hb)
      (resolvedTerminalPositiveChart_subset_terminal A D r ha0 ha)).symm
  case terminalPositive.terminalPositive ha0 ha hb0 hb =>
    exact (hij rfl).elim
  case terminalPositive.terminalNegative ha0 ha hb0 hb =>
    exact (resolvedTerminalCharts_disjoint A D r ha0 ha).symm
  case terminalPositive.terminalMiddle ha0 ha hb0 hb =>
    omega
  case terminalNegative.identity ha0 ha =>
    exact ((resolvedTerminal_identity_disjoint A D ha0).mono_left
      (resolvedTerminalNegativeChart_subset_terminal A D r ha0 ha))
  case terminalNegative.retainedPositive ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r b hb0 hb)
      (resolvedTerminalNegativeChart_subset_terminal A D r ha0 ha)).symm
  case terminalNegative.retainedNegative ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r b hb0 hb)
      (resolvedTerminalNegativeChart_subset_terminal A D r ha0 ha)).symm
  case terminalNegative.terminalPositive ha0 ha hb0 hb =>
    exact (resolvedTerminalCharts_disjoint A D r ha0 ha)
  case terminalNegative.terminalNegative ha0 ha hb0 hb =>
    exact (hij rfl).elim
  case terminalNegative.terminalMiddle ha0 ha hb0 hb =>
    omega
  case terminalMiddle.identity ha0 ha =>
    exact ((resolvedTerminal_identity_disjoint A D ha0).mono_left
      ((resolvedTerminalMiddleChart_range A D r ha0 ha).subset))
  case terminalMiddle.retainedPositive ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedPositiveChart_subset_boundary A D r b hb0 hb)
      ((resolvedTerminalMiddleChart_range A D r ha0 ha).subset)).symm
  case terminalMiddle.retainedNegative ha0 ha b hb0 hb =>
    exact ((resolvedRetainedBoundary_terminal_disjoint A D b hb).mono
      (resolvedRetainedNegativeChart_subset_boundary A D r b hb0 hb)
      ((resolvedTerminalMiddleChart_range A D r ha0 ha).subset)).symm
  case terminalMiddle.terminalPositive ha0 ha hb0 hb =>
    omega
  case terminalMiddle.terminalNegative ha0 ha hb0 hb =>
    omega
  case terminalMiddle.terminalMiddle ha0 ha hb0 hb =>
    exact (hij rfl).elim

/-- The actual arithmetic charts are pairwise disjoint inside the entire smooth fiber. -/
theorem resolvedComponentCharts_disjoint (i j : ResolvedComponentIndex depth) (hij : i ≠ j) :
    Disjoint (Set.range (resolvedComponentChart A D r i))
      (Set.range (resolvedComponentChart A D r j)) := by
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hi := (resolvedComponentChart_mem_range_iff A D r i z).mp hi
  have hj := (resolvedComponentChart_mem_range_iff A D r j z).mp hj
  rw [resolvedComponentChart_range_inclusion] at hi hj
  exact Set.disjoint_left.mp (resolvedComponentCarriers_disjoint A D r i j hij) hi hj

end FLT.Mazur.WeierstrassDividedDepth
