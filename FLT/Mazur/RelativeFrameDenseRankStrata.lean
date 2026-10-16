/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameUniformRank
public import Mathlib.Data.Nat.Find

/-!
# Dense coverage by original rank strata

The constructed rank strata cover a dense open of a noetherian original base.
The proof maximizes the actual frame rank on each nonempty open and excludes
the closure of larger-frame images there. It does not cover the residual closed set.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [NoetherianSpace S]

/-- Every nonempty original open meets one of the actual rank strata. -/
theorem exists_rankStratum_in_open (U : S.Opens) (hU : (U : Set S).Nonempty) :
    ∃ (n : ℕ) (x : S), x ∈ U ∧ x ∈ rankStratumOpen E n := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  let P (n : ℕ) : Prop := ∃ x : S, x ∈ U ∧ x ∈ rankImageOpen E n
  obtain ⟨x, hx⟩ := hU
  obtain ⟨n, hn⟩ := exists_point_rank E x
  have hxn := (hn n).mpr le_rfl
  have hnN := hN x n hxn
  let k := Nat.findGreatest P N
  obtain ⟨y, hyU, hyk⟩ := Nat.findGreatest_spec hnN (show P n from ⟨x, hx, hxn⟩)
  have hbad : (rankImageOpen E (k + 1) : Set S) ⊆ (U : Set S)ᶜ := by
    intro z hz hzU
    have hle := hN z (k + 1) hz
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hle ⟨z, hzU, hz⟩
  refine ⟨k, y, hyU, hyk, ?_⟩
  intro hyclosure
  exact closure_minimal hbad U.isOpen.isClosed_compl hyclosure hyU

/-- The union of the constructed original rank strata is dense. -/
theorem rankStrata_dense : Dense (⋃ n : ℕ, (rankStratumOpen E n : Set S)) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨n, x, hxU, hxn⟩ := exists_rankStratum_in_open E ⟨U, hU⟩ hne
  exact ⟨x, hxU, Set.mem_iUnion.mpr ⟨n, hxn⟩⟩

/-- The dense covered region is an actual open in the unchanged original base. -/
def rankStrataOpen : S.Opens := ⨆ n : ℕ, rankStratumOpen E n

/-- The uncovered original locus is closed with empty interior. -/
theorem rankStrata_complement_interior :
    interior ((rankStrataOpen E : Set S)ᶜ) = ∅ := by
  have hd := rankStrata_dense E
  rw [dense_iff_closure_eq] at hd
  rw [rankStrataOpen, TopologicalSpace.Opens.coe_iSup]
  rw [interior_compl, hd, Set.compl_univ]

end FLT.Mazur.RelativeOrderedTuples
