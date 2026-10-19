/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStageSectionDetection

/-!
# Detecting residual equations outside an already solved rank

An equation valid on an open containing the matching rank holds on every
thickening of that rank, with its full nilpotent structure. On a locally
Noetherian coefficient scheme, only the higher rank equations remain to be
checked. Every failure has a finite higher-rank order witnessing it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (b : B ⟶ S) (n : ℕ) (O : B.Opens)

/-- Open equations pull back to every thickening supported on the solved rank. -/
theorem rankStage_eq_of_open
    (hO : ∀ x : B, b x ∈ exactRank E n → x ∈ O)
    (a c : Γ(B, ⊤)) (hac : O.ι.appTop a = O.ι.appTop c) (k : ℕ) :
    (rankPullbackMap E b n k).appTop a = (rankPullbackMap E b n k).appTop c := by
  let j := rankPullbackMap E b n k
  have hr : Set.range j ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hO _ (rankPullback_endpoint E b n k y)
  change j.appTop a = j.appTop c
  rw [← IsOpenImmersion.lift_fac O.ι j hr, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hac]

variable [IsNoetherian S] [IsLocallyNoetherian B]

/-- Matching-rank open equations reduce full equality to bounded higher-rank equations. -/
theorem section_eq_iff_higher_rank_stages (N : ℕ)
    (hcover : ∀ x : B, ∃ m : ℕ, n ≤ m ∧ m ≤ N ∧ b x ∈ exactRank E m)
    (hO : ∀ x : B, b x ∈ exactRank E n → x ∈ O)
    (a c : Γ(B, ⊤)) (hac : O.ι.appTop a = O.ι.appTop c) :
    a = c ↔ ∀ m : ℕ, n < m → m ≤ N → ∀ k : ℕ,
      (rankPullbackMap E b m k).appTop a = (rankPullbackMap E b m k).appTop c := by
  constructor
  · rintro rfl m _ _ k
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply section_zero_of_bounded_rank_stages E b n N hcover (a - c)
    intro m hnm hm k
    rw [map_sub, sub_eq_zero]
    rcases hnm.eq_or_lt with rfl | hnm
    · exact rankStage_eq_of_open E b n O hO a c hac k
    · exact h m hnm hm k

/-- A nonzero residual discrepancy survives on a finite higher-rank thickening. -/
theorem exists_higher_rank_discrepancy (N : ℕ)
    (hcover : ∀ x : B, ∃ m : ℕ, n ≤ m ∧ m ≤ N ∧ b x ∈ exactRank E m)
    (hO : ∀ x : B, b x ∈ exactRank E n → x ∈ O)
    (a c : Γ(B, ⊤)) (hac : O.ι.appTop a = O.ι.appTop c) (hne : a ≠ c) :
    ∃ m : ℕ, n < m ∧ m ≤ N ∧ ∃ k : ℕ,
      (rankPullbackMap E b m k).appTop a ≠ (rankPullbackMap E b m k).appTop c := by
  by_contra h
  push Not at h
  exact hne ((section_eq_iff_higher_rank_stages E b n O N hcover hO a c hac).mpr h)

end FLT.Mazur.RelativeOrderedTuples
