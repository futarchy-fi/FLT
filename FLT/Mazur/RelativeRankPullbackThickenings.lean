/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStratumThickenings
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Rank thickenings over an unchanged coefficient scheme

Base change every infinitesimal rank stage to the supplied coefficient scheme.
These actual schemes cover all its points, and their complete-frame covers split
its entire original relation. No reduction of the coefficient scheme is taken.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (b : B ⟶ S) (n k : ℕ)

/-- Pull the full ideal-power rank stage to the original coefficient scheme. -/
def rankPullbackThickening : Scheme := pullback (rankThickeningMap E n k) b

/-- Its map retains the original coefficient point. -/
def rankPullbackMap : rankPullbackThickening E b n k ⟶ B := pullback.snd _ _

omit [QuasiCompact E.hom] in
/-- Its image is exactly the original rank piece, including all residual points. -/
theorem rankPullbackMap_range :
    Set.range (rankPullbackMap E b n k) = b ⁻¹' exactRank E n := by
  change Set.range (pullback.snd (rankThickeningMap E n k) b) = _
  rw [Scheme.Pullback.range_snd, rankThickeningMap_range]

omit [QuasiCompact E.hom] in
/-- The original endpoint of every stage has its stated exact rank. -/
theorem rankPullback_endpoint (x : rankPullbackThickening E b n k) :
    b (rankPullbackMap E b n k x) ∈ exactRank E n := by
  have hx := Set.mem_range_self (f := rankPullbackMap E b n k) x
  rw [rankPullbackMap_range] at hx
  exact hx

/-- Every coefficient point lifts to a stage at each chosen infinitesimal order. -/
theorem exists_rankPullback_lift (x : B) :
    ∃ (n : ℕ) (y : rankPullbackThickening E b n k), rankPullbackMap E b n k y = x := by
  obtain ⟨n, hn⟩ := exists_exactRank E (b x)
  have hx : x ∈ Set.range (rankPullbackMap E b n k) := by
    rw [rankPullbackMap_range]
    exact hn
  obtain ⟨y, hy⟩ := hx
  exact ⟨n, y, hy⟩

omit [QuasiCompact E.hom] in
/-- The constructed original frame cover is surjective over every thickened stage. -/
theorem rankPullback_frameCover_surjective :
    Function.Surjective
      (rankFrameProjection E n (rankPullbackMap E b n k ≫ b)) := by
  apply rankFrameProjection_surjective
  rintro _ ⟨x, rfl⟩
  exact rankPullback_endpoint E b n k x

/-- The full original relation splits, preserving every coefficient on the chosen stage. -/
def rankPullbackSplitIso :
    (∐ fun _ : Fin n ↦ rankFrameCover E n (rankPullbackMap E b n k ≫ b)) ≅
      pullback E.hom
        (rankFrameProjection E n (rankPullbackMap E b n k ≫ b) ≫
          rankPullbackMap E b n k ≫ b) :=
  rankFrameCoverIso E n (rankPullbackMap E b n k ≫ b) (by
    rintro _ ⟨x, rfl⟩
    exact rankPullback_endpoint E b n k x)

end FLT.Mazur.RelativeOrderedTuples
