/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPrecedingExterior
public import FLT.Mazur.WeierstrassDividedTerminalAllExteriorNodes

/-!
# The initial ordered nodes remain distinct from all later nodes

The original initial chart lies in every preceding exterior. The established
node exclusions therefore separate both initial origins from the retained pairs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- The original ordered initial pair as scheme maps, before taking their images. -/
def orderedInitialSection (t : ℕ) (ht : t ≤ n) (hstart : 0 < start)
    (hk : 2 * start ≤ depth) (i : Fin 2) :
    Spec (.of K) ⟶ finiteGlobalTensorModel hπ data K t ht :=
  Fin.cases (initialGlobalFirstSection hπ data D t ht hstart hk)
    (fun _ => initialGlobalSecondSection hπ data D t ht hstart hk) i

/-- Both original initial origins lie in the full original initial tensor chart. -/
theorem orderedInitialSections_range (t : ℕ) (ht : t ≤ n) (hstart : 0 < start)
    (hk : 2 * start ≤ depth) (i : Fin 2) :
    Set.range (orderedInitialSection hπ data D t ht hstart hk i) ⊆
        Set.range (globalInitialTensorChart hπ data K t ht) := by
  fin_cases i <;> rintro _ ⟨x, rfl⟩ <;> exact ⟨_, rfl⟩

/-- The original initial pair misses both retained sections at every later depth. -/
theorem orderedInitialSections_retained_disjoint (t : ℕ) (ht : t ≤ n)
    (hstart : 0 < start) (j : ℕ) (hj : j + 1 ≤ t)
    (hk : 2 * (start + j + 1) ≤ depth) (a b : Fin 2) :
    Disjoint
      (Set.range (orderedInitialSection hπ data D t ht hstart (by omega) a))
      (Set.range (retainedNodeSectionAt hπ data D t ht j hj hk b)) := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedNodeSectionAt_original hπ data D j (by omega),
    orderedRetainedSection_positive hπ data D j (by omega) r ht hk (by omega)]
  have H := (orderedInitialSections_range hπ data D (j + 1 + r) ht hstart (by omega) a)
  have H := H.trans (globalInitialTensorChart_preceding_range hπ data K j (by omega) r ht)
  fin_cases b
  · exact (olderGlobalFirstSectionExterior_disjoint hπ data D j (by omega) r ht
      (by omega) hk).mono_left H
  · exact (olderGlobalSecondSectionExterior_disjoint hπ data D j (by omega) r ht
      (by omega) hk).mono_left H

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)

/-- Both initial origins miss every retained node in the fixed family. -/
theorem finalNodeSection_initial_retained_disjoint
    (a : {_i : Fin 2 // 0 < start}) (j : Fin (s + 1)) (b : Fin 2) :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inl a))))
      (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (j, b))))) :=
  orderedInitialSections_retained_disjoint hπ data D (s + 1) hs a.property j.val
    (by omega) (by omega) a.val b

/-- The terminal origin also misses both original initial nodes. -/
theorem finalNodeSection_terminal_initial_disjoint (a : {_i : Fin 2 // 0 < start}) :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())))
      (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inl a)))) := by
  have H := terminalNode_globalExteriorIndex_disjoint hπ data D s hs hk hp
    ⟨s + 1, by omega⟩
  apply H.mono_right
  have hr := orderedInitialSections_range hπ data D (s + 1) hs a.property (by omega) a.val
  rw [globalInitialTensorChart_range_index] at hr
  exact hr

end FLT.Mazur.WeierstrassDividedDepth
