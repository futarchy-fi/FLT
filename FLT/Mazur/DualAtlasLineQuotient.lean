/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasLineClassification

/-!
# Dual projective atlas sections represent line subbundle classes

The parameter data are original rank-one sheaves and locally split maps.
The quotient relation is an actual source isomorphism commuting with the
maps, and the equivalence uses the constructed scheme atlas in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasLineQuotient
open FCurve SplitLineAffineNeighborhood LocallySplitLineAtlasSection
variable {X : Scheme.{u}} (M : X.Modules)

/-- Actual line subbundle data retaining the source sheaf. -/
structure Line where
  /-- The original line sheaf. -/
  source : X.Modules
  /-- Local freeness of rank one. -/
  rankOne : LocallyFreeRankOne source
  /-- Its map into the given ambient sheaf. -/
  inclusion : source ⟶ M
  /-- Local retractions of the original map. -/
  locallySplit : LocallySplit inclusion

/-- Isomorphisms of the retained source lines, preserving the inclusions. -/
def lineSetoid : Setoid (Line M) where
  r a b := ∃ e : a.source ≅ b.source, e.hom ≫ b.inclusion = a.inclusion
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨Iso.refl _, Category.id_comp _⟩
    · rintro a b ⟨e, he⟩
      exact ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩
    · rintro a b c ⟨e, he⟩ ⟨d, hd⟩
      exact ⟨e ≪≫ d, by simp only [Iso.trans_hom, Category.assoc, hd, he]⟩

variable (hM : LocallyFiniteFree M)

/-- Sections of the actual dual projective atlas projection. -/
abbrev Section := {p : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM //
  p ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X}

/-- The geometric atlas section of an original locally split inclusion. -/
def toSection (a : Line M) : Section M hM :=
  ⟨morphism a.inclusion a.rankOne a.locallySplit hM,
    morphism_projection a.inclusion a.rankOne a.locallySplit hM⟩

/-- The forward construction retains its actual glued source and inclusion. -/
def fromSection (p : Section M hM) : Line M where
  source := DualAtlasSectionForwardLine.line M hM p.val p.property
  rankOne := DualAtlasSectionForwardLine.rankOne M hM p.val p.property
  inclusion := DualAtlasSectionForwardLine.inclusion M hM p.val p.property
  locallySplit := DualAtlasSectionForwardLine.locallySplit M hM p.val p.property

/-- The original scheme section is recovered from its constructed line. -/
lemma toSection_fromSection (p : Section M hM) :
    toSection M hM (fromSection M hM p) = p :=
  Subtype.ext (DualAtlasSectionForwardLine.reverse_forward M hM p.val p.property)

/-- Equality of geometric sections is exactly the original source-isomorphism relation. -/
lemma toSection_eq_iff (a b : Line M) :
    toSection M hM a = toSection M hM b ↔ (lineSetoid M).r a b := by
  rw [Subtype.ext_iff]
  exact morphism_eq_iff_sourceIso a.inclusion b.inclusion
    a.rankOne b.rankOne a.locallySplit b.locallySplit hM

/-- The geometric map descends through actual source isomorphisms. -/
def quotientToSection : Quotient (lineSetoid M) → Section M hM :=
  Quotient.lift (toSection M hM) (fun a b h ↦ (toSection_eq_iff M hM a b).mpr h)

/-- The actual dual atlas classifies locally split line inclusions. -/
def quotientEquiv : Quotient (lineSetoid M) ≃ Section M hM where
  toFun := quotientToSection M hM
  invFun p := Quotient.mk _ (fromSection M hM p)
  left_inv q := by
    induction q using Quotient.inductionOn with | h a =>
      exact Quotient.sound ((toSection_eq_iff M hM _ _).mp
        (toSection_fromSection M hM (toSection M hM a)))
  right_inv := toSection_fromSection M hM

end FLT.Mazur.DualAtlasLineQuotient
