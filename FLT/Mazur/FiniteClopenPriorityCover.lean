/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Order.Disjointed

/-!
# A fixed disjoint refinement of a finite clopen cover

The first open containing a point determines its piece. This construction
commutes with preimages, so one ordering gives coordinated partitions across
all infinitesimal orders and preserves full relation invariance.
-/

@[expose] public noncomputable section
open TopologicalSpace
namespace FLT.Mazur.FiniteClopenPriorityCover
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {m : ℕ}
  (U : Fin m → Opens X) (hU : ∀ i, IsClosed (U i : Set X))

include hU in
/-- Removing all earlier chart domains from one clopen leaves a clopen piece. -/
theorem disjointed_isClopen (i : Fin m) :
    IsClopen (disjointed (fun j ↦ (U j : Set X)) i) :=
  disjointedRec (fun {_t j} ht ↦ ht.inter (IsClopen.compl ⟨hU j, (U j).isOpen⟩))
    ⟨hU i, (U i).isOpen⟩

/-- The first-chart piece is an actual open, retaining its full set of points. -/
def piece (i : Fin m) : Opens X :=
  ⟨disjointed (fun j ↦ (U j : Set X)) i, (disjointed_isClopen U hU i).isOpen⟩

/-- The piece remains closed. -/
theorem piece_isClosed (i : Fin m) : IsClosed (piece U hU i : Set X) :=
  (disjointed_isClopen U hU i).isClosed

/-- Membership selects the earliest chart containing the point. -/
theorem mem_piece (i : Fin m) (x : X) :
    x ∈ piece U hU i ↔ x ∈ U i ∧ ∀ j, j < i → x ∉ U j := by
  change x ∈ disjointed (fun j ↦ (U j : Set X)) i ↔ _
  rw [disjointed_eq_inf_compl]
  change (x ∈ U i ∧ x ∈ ⋂ j, ⋂ (_ : j < i), (U j : Set X)ᶜ) ↔ _
  simp only [Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe]

/-- Every piece stays in its named original chart. -/
theorem piece_le (i : Fin m) : piece U hU i ≤ U i :=
  disjointed_le (fun j ↦ (U j : Set X)) i

/-- Different pieces have empty intersection. -/
theorem piece_inf_eq_bot {i j : Fin m} (h : i ≠ j) : piece U hU i ⊓ piece U hU j = ⊥ := by
  apply SetLike.coe_injective
  exact (disjoint_disjointed (fun j ↦ (U j : Set X)) h).eq_bot

/-- The coordinated pieces cover exactly the same locus as the original charts. -/
theorem iSup_piece : (⨆ i, piece U hU i) = ⨆ i, U i := by
  apply SetLike.coe_injective
  simp only [Opens.coe_iSup]
  exact iUnion_disjointed (f := fun j ↦ (U j : Set X))

/-- One fixed priority ordering is preserved by every map preserving the original domains. -/
theorem preimage_piece (V : Fin m → Opens Y) (hV : ∀ i, IsClosed (V i : Set Y))
    (f : Y → X) (hf : ∀ i, f ⁻¹' (U i : Set X) = (V i : Set Y)) (i : Fin m) :
    f ⁻¹' (piece U hU i : Set X) = (piece V hV i : Set Y) := by
  ext x
  have hmem (j : Fin m) : f x ∈ U j ↔ x ∈ V j :=
    Iff.of_eq (congrArg (fun W : Set Y ↦ x ∈ W) (hf j))
  change f x ∈ piece U hU i ↔ x ∈ piece V hV i
  simp only [mem_piece, hmem]

end FLT.Mazur.FiniteClopenPriorityCover
