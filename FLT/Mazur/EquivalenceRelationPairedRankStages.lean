/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankSaturation
public import FLT.Mazur.RelativeRankThickeningFinite
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Both endpoints of full original relation rank stages

The actual arrow in a double restriction identifies the endpoint ranks on
every unsplit ideal-power stage. Both entire source pullbacks are finite.
This concerns the original relation, not arbitrary pairs agreeing on scalars.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationRestriction
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q) (k : Y ⟶ A)
local instance pairedStageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance pairedStageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance pairedStageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] doubleDomain fst snd arrow
local notation "x" => fst p q k ≫ k
local notation "y" => snd p q k ≫ k
local notation "ι" => rankPullbackMap (Over.mk p) x

include e in
/-- Both independent source lifts retain exactly the same original rank. -/
theorem double_exactRank_iff (n : ℕ) (z : doubleDomain p q k) :
    x z ∈ exactRank (Over.mk p) n ↔ y z ∈ exactRank (Over.mk p) n := by
  rw [← arrow_fst, ← arrow_snd]
  exact exactRank_endpoint_iff e n (arrow p q k z)

include e in
/-- The second endpoint has the prescribed rank on the whole first-endpoint thickening. -/
theorem rankPullback_second_exactRank (n r : ℕ) :
    Set.range (ι n r ≫ y) ⊆ exactRank (Over.mk p) n := by
  rintro _ ⟨z, rfl⟩
  exact (double_exactRank_iff e k n (ι n r z)).mp
    (rankPullback_endpoint (Over.mk p) x n r z)

omit [QuasiCompact p] in
/-- Rank-stage restriction preserves both endpoints of the actual original arrow. -/
theorem rankPullback_original_arrow (n r : ℕ) :
    (ι n r ≫ arrow p q k) ≫ p = ι n r ≫ x ∧
      (ι n r ≫ arrow p q k) ≫ q = ι n r ≫ y := by
  constructor
  · rw [Category.assoc, arrow_fst]
  · rw [Category.assoc, arrow_snd]

variable [LocallyQuasiFinite p]
local instance pairedStageOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›

include e in
/-- Both whole original sources are finite, with the full stage's nilpotents retained. -/
theorem rankPullback_both_sources_finite (n r : ℕ) :
    IsFinite (pullback.snd p (ι n r ≫ x)) ∧
      IsFinite (pullback.snd p (ι n r ≫ y)) := by
  exact ⟨finite_pullback_rankPullback (Over.mk p) x n r,
    finite_pullback_of_exactRank (Over.mk p) n _
      (rankPullback_second_exactRank e k n r)⟩

end FLT.Mazur.SchemeRelationRestriction
