/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankOneSection
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts

/-!
# Original identity arrows on full rank-one tests

Reflexivity supplies the singleton frame. On every test supported on the
closed rank-one bound, the entire original first-source pullback is an
isomorphism and every relation arrow is its identity section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance oneTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance oneTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance oneTestOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

omit [IsSeparated p] [Etale p] [QuasiCompact p] in
/-- The original identity arrow is a section over every unchanged coefficient test. -/
def originalIdentityTest (b : B ⟶ A) : Over.mk b ⟶ Over.mk p :=
  Over.homMk (b ≫ e.r) (by
    change (b ≫ e.r) ≫ p = b
    rw [Category.assoc, e.reflexivity₁, Category.comp_id])

variable (b : B ⟶ A) (hb : Set.range b ⊆ rankAtMost (Over.mk p) 1)
include e hb

/-- The full original source over a rank-one test is its coefficient scheme. -/
theorem original_rankOne_source_isIso : IsIso (pullback.snd p b) :=
  rankOne_pullback_isIso (Over.mk p) (originalIdentityTest e b) hb

/-- The whole original source factors through its actual identity section. -/
theorem original_rankOne_source_fst :
    pullback.fst p b = pullback.snd p b ≫ b ≫ e.r :=
  rankOne_pullback_fst (Over.mk p) (originalIdentityTest e b) hb

/-- Every original arrow over a rank-one coefficient test is the identity arrow. -/
theorem original_rankOne_arrow_identity {T : Scheme.{0}} (d : T ⟶ D) (v : T ⟶ B)
    (h : d ≫ p = v ≫ b) : d = v ≫ b ≫ e.r :=
  rankOne_arrow_eq (Over.mk p) (originalIdentityTest e b) hb d v h

/-- Both complete original endpoints agree on the full rank-one source. -/
theorem original_rankOne_source_endpoints :
    pullback.fst p b ≫ q = pullback.snd p b ≫ b := by
  rw [original_rankOne_source_fst e b hb, Category.assoc, Category.assoc,
    e.reflexivity₂, Category.comp_id]

/-- Rank-one identity is an equality of morphisms, not merely of geometric endpoints. -/
theorem original_rankOne_arrow_endpoints {T : Scheme.{0}} (d : T ⟶ D) (v : T ⟶ B)
    (h : d ≫ p = v ≫ b) : d ≫ q = v ≫ b := by
  rw [original_rankOne_arrow_identity e b hb d v h, Category.assoc, Category.assoc,
    e.reflexivity₂, Category.comp_id]

end FLT.Mazur.EquivalenceRelationOrderedFrames
