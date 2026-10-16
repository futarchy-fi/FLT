/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankImage
public import Mathlib.Topology.NoetherianSpace

/-!
# A uniform finite bound for original frame ranks

Over a noetherian base, finitely many generic points bound every etale frame
image. Each generic bound comes from the entire geometric fiber enumeration.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [NoetherianSpace S]

/-- A single finite bound controls all original distinct-frame fibers. -/
theorem exists_uniform_rank_bound :
    ∃ N : ℕ, ∀ (x : S) (m : ℕ), x ∈ rankImageOpen E m → m ≤ N := by
  classical
  have hG := genericPoints.finite
    (NoetherianSpace.finite_irreducibleComponents (α := S))
  let _ := hG.fintype
  choose n hn using fun x : genericPoints S ↦ exists_point_rank E x.val
  refine ⟨Finset.univ.sup n, ?_⟩
  intro x m hx
  have hd : Dense (genericPoints S) := by
    rw [dense_iff_closure_eq]
    exact genericPoints.closure
  obtain ⟨y, hy, hym⟩ := hd.exists_mem_open (rankImageOpen E m).isOpen ⟨x, hx⟩
  exact ((hn ⟨y, hy⟩ m).mp hym).trans (Finset.le_sup (f := n) (Finset.mem_univ _))

/-- Beyond a constructed uniform bound the actual original frame image is empty. -/
theorem exists_empty_rank_image : ∃ N : ℕ, rankImageOpen E (N + 1) = ⊥ := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, ?_⟩
  apply le_antisymm _ bot_le
  intro x hx
  exact (Nat.not_succ_le_self N (hN x (N + 1) hx)).elim

end FLT.Mazur.RelativeOrderedTuples
