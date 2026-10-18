/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeExactRankFrameCover
public import FLT.Mazur.RelativeFrameCompleteFinite
public import FLT.Mazur.SchemeFiniteTargetFppfBaseChange

/-!
# Finiteness on unsplit exact-rank coefficient schemes

The constructed complete-frame cover makes the whole original source finite.
Finiteness descends to the unchanged coefficient scheme. Neither a chosen
frame nor flatness of the coefficient scheme over the original base is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] distinctScheme rankFrameCover rankFrameProjection rankCoverFrame
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [LocallyQuasiFinite E.hom]
  (n : ℕ) {B : Scheme} (b : B ⟶ S)

/-- Exact rank makes the full original pullback finite before any frame is selected. -/
theorem finite_pullback_of_exactRank (hb : Set.range b ⊆ exactRank E n) :
    IsFinite (pullback.snd E.hom b) := by
  let g := rankFrameProjection E n b
  let _ : Etale g := rankFrameProjection_etale E n b
  have ht : Set.range (g ≫ b) ⊆ rankAtMost E n := by
    rintro _ ⟨x, rfl⟩
    exact (hb (Set.mem_range_self (g x))).2
  let _ := finite_pullback_of_complete E (Fin n) (rankCoverFrame E n b)
    (frame_range_complete_of_rankAtMost E n (rankCoverFrame E n b) ht)
  let _ : IsFinite (pullback.snd (pullback.snd E.hom b) g) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd E.hom b g]
    infer_instance
  apply (finiteTargetOpen_eq_top_iff (pullback.snd E.hom b)).mp
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := rankFrameProjection_surjective E n b hb x
  apply (mem_finiteTargetOpen_fppf_iff
    (IsPullback.of_hasPullback (pullback.snd E.hom b) g) y).mp
  rw [finiteTargetOpen_eq_top]
  trivial

/-- A flat finitely presented exact-rank test can meet only the original finite locus. -/
theorem exactRank_flat_range_le_finiteTarget [Flat b] [LocallyOfFinitePresentation b]
    (hb : Set.range b ⊆ exactRank E n) : Set.range b ⊆ finiteTargetOpen E.hom := by
  let _ := finite_pullback_of_exactRank E n b hb
  rintro _ ⟨x, rfl⟩
  apply (mem_finiteTargetOpen_fppf_iff (IsPullback.of_hasPullback E.hom b) x).mp
  rw [finiteTargetOpen_eq_top]
  trivial

/-- At a residual point the exact-rank coefficient map cannot be flat and finitely presented. -/
theorem exactRank_not_flat_at_residual [LocallyOfFinitePresentation b]
    (hb : Set.range b ⊆ exactRank E n) (x : B)
    (hx : b x ∉ finiteTargetOpen E.hom) : ¬ Flat b := by
  intro h
  let _ := h
  exact hx (exactRank_flat_range_le_finiteTarget E n b hb (Set.mem_range_self x))

end FLT.Mazur.RelativeOrderedTuples
