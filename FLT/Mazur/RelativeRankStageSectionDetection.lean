/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInfinitesimalPointDetection
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Full coefficient detection by all infinitesimal rank stages

For locally Noetherian coefficients, the full collection of rank stages is
jointly injective on global sections. Each infinitesimal point test factors
through a finite original rank order. The orders may depend on the point test;
no single finite order, flat stage cover, or existence of lifts is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeInfinitesimalPointDetection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] (b : B ⟶ S)

/-- Every full infinitesimal point test factors through some original rank order. -/
theorem infinitesimalPoint_rank_factor (x : B) (m k : ℕ)
    (hx : b x ∈ exactRank E m) :
    ∃ (order : ℕ) (g : pointThickening B x k ⟶ rankPullbackThickening E b m order),
      g ≫ rankPullbackMap E b m order = pointThickeningMap B x k := by
  apply exists_rankPullback_factor E m b (pointThickeningMap B x k)
  rintro _ ⟨y, rfl⟩
  change b (pointThickeningMap B x k y) ∈ exactRank E m
  rw [pointThickeningMap_apply]
  exact hx

/-- Stage vanishing at one rank kills all infinitesimal tests at its original points. -/
theorem infinitesimalPoint_zero_of_rank_stages (a : Γ(B, ⊤)) (x : B) (m : ℕ)
    (hx : b x ∈ exactRank E m)
    (ha : ∀ order : ℕ, (rankPullbackMap E b m order).appTop a = 0) (k : ℕ) :
    (pointThickeningMap B x k).appTop a = 0 := by
  obtain ⟨order, g, hg⟩ := infinitesimalPoint_rank_factor E b x m k hx
  rw [← hg, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ha, map_zero]

variable [IsLocallyNoetherian B]

/-- All stages at a point's original rank detect its full coefficient germ. -/
theorem germ_zero_of_rank_stages (a : Γ(B, ⊤)) (x : B) (m : ℕ)
    (hx : b x ∈ exactRank E m)
    (ha : ∀ order : ℕ, (rankPullbackMap E b m order).appTop a = 0) :
    B.presheaf.germ ⊤ x trivial a = 0 :=
  germ_eq_zero B x a (infinitesimalPoint_zero_of_rank_stages E b a x m hx ha)

/-- Any set of ranks covering the original coefficient points detects full sections. -/
theorem section_zero_of_rank_stages (ranks : Set ℕ)
    (hcover : ∀ x : B, ∃ m ∈ ranks, b x ∈ exactRank E m) (a : Γ(B, ⊤))
    (ha : ∀ m ∈ ranks, ∀ order : ℕ, (rankPullbackMap E b m order).appTop a = 0) :
    a = 0 := by
  apply section_eq_zero B a
  intro x k
  obtain ⟨m, hm, hx⟩ := hcover x
  exact infinitesimalPoint_zero_of_rank_stages E b a x m hx (ha m hm) k

/-- Equality, including nilpotent coefficients, descends from every retained rank order. -/
theorem section_eq_of_rank_stages (ranks : Set ℕ)
    (hcover : ∀ x : B, ∃ m ∈ ranks, b x ∈ exactRank E m) (a c : Γ(B, ⊤))
    (hac : ∀ m ∈ ranks, ∀ order : ℕ,
      (rankPullbackMap E b m order).appTop a = (rankPullbackMap E b m order).appTop c) :
    a = c := by
  apply sub_eq_zero.mp
  apply section_zero_of_rank_stages E b ranks hcover (a - c)
  intro m hm order
  rw [map_sub, hac m hm order, sub_self]

/-- Bounded rank coverage requires only the stated finite interval of original stages. -/
theorem section_zero_of_bounded_rank_stages (lo hi : ℕ)
    (hcover : ∀ x : B, ∃ m : ℕ, lo ≤ m ∧ m ≤ hi ∧ b x ∈ exactRank E m)
    (a : Γ(B, ⊤))
    (ha : ∀ m : ℕ, lo ≤ m → m ≤ hi → ∀ order : ℕ,
      (rankPullbackMap E b m order).appTop a = 0) : a = 0 := by
  refine section_zero_of_rank_stages E b (Set.Icc lo hi) ?_ a ?_
  · intro x
    obtain ⟨m, hlo, hhi, hx⟩ := hcover x
    exact ⟨m, ⟨hlo, hhi⟩, hx⟩
  · intro m hm
    exact ha m hm.1 hm.2

end FLT.Mazur.RelativeOrderedTuples
