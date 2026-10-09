/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTripleOverlap
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Triple overlaps of three independent scheme morphisms

The adjacent-pair presentation retains all three original pair projections.
Pasting compares it with an iterated fiber product over the common base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFamilyTripleOverlap
variable {X Y₁ Y₂ Y₃ : Scheme.{u}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (h : Y₃ ⟶ X)

/-- Three independent members, with their common middle coordinate identified. -/
abbrev triple : Scheme.{u} :=
  Limits.pullback (Limits.pullback.snd f g) (Limits.pullback.fst g h)

/-- The first adjacent pair of original members. -/
abbrev pair12 : triple f g h ⟶ Limits.pullback f g := Limits.pullback.fst _ _

/-- The second adjacent pair of original members. -/
abbrev pair23 : triple f g h ⟶ Limits.pullback g h := Limits.pullback.snd _ _

/-- The first original coordinate. -/
abbrev coord1 : triple f g h ⟶ Y₁ := pair12 f g h ≫ Limits.pullback.fst f g

/-- The middle original coordinate. -/
abbrev coord2 : triple f g h ⟶ Y₂ := pair12 f g h ≫ Limits.pullback.snd f g

/-- The last original coordinate. -/
abbrev coord3 : triple f g h ⟶ Y₃ := pair23 f g h ≫ Limits.pullback.snd g h

/-- Both adjacent pairs retain the same middle member. -/
@[reassoc]
lemma pair23_fst : pair23 f g h ≫ Limits.pullback.fst g h = coord2 f g h :=
  Limits.pullback.condition.symm

/-- The outer original coordinates have equal images in the base. -/
lemma coord13_base : coord1 f g h ≫ f = coord3 f g h ≫ h := by
  have hm : pair12 f g h ≫ Limits.pullback.snd f g =
      pair23 f g h ≫ Limits.pullback.fst g h := Limits.pullback.condition
  simp only [coord1, coord3, Category.assoc]
  rw [Limits.pullback.condition, ← Category.assoc, hm, Category.assoc,
    Limits.pullback.condition]

/-- The outer original pair. -/
def pair13 : triple f g h ⟶ Limits.pullback f h :=
  Limits.pullback.lift (coord1 f g h) (coord3 f g h) (coord13_base f g h)

@[reassoc (attr := simp)]
lemma pair13_fst : pair13 f g h ≫ Limits.pullback.fst f h = coord1 f g h :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pair13_snd : pair13 f g h ≫ Limits.pullback.snd f h = coord3 f g h :=
  Limits.pullback.lift_snd _ _ _

/-- Pasting expresses the triple as a fiber product of the first pair and last member. -/
def pasteIso : triple f g h ≅ Limits.pullback (Limits.pullback.snd f g ≫ g) h :=
  Limits.pullbackRightPullbackFstIso g h (Limits.pullback.snd f g)

@[reassoc (attr := simp)]
lemma pasteIso_hom_fst :
    (pasteIso f g h).hom ≫ Limits.pullback.fst _ _ = pair12 f g h :=
  Limits.pullbackRightPullbackFstIso_hom_fst _ _ _

@[reassoc (attr := simp)]
lemma pasteIso_hom_snd :
    (pasteIso f g h).hom ≫ Limits.pullback.snd _ _ = coord3 f g h :=
  Limits.pullbackRightPullbackFstIso_hom_snd _ _ _

@[reassoc (attr := simp)]
lemma pasteIso_inv_pair12 :
    (pasteIso f g h).inv ≫ pair12 f g h = Limits.pullback.fst _ _ :=
  Limits.pullbackRightPullbackFstIso_inv_fst _ _ _

@[reassoc (attr := simp)]
lemma pasteIso_inv_coord3 :
    (pasteIso f g h).inv ≫ coord3 f g h = Limits.pullback.snd _ _ :=
  Limits.pullbackRightPullbackFstIso_inv_snd_snd _ _ _

end FLT.Mazur.SchemeFamilyTripleOverlap
