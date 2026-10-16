/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiberRebase

/-!
# Transporting all original sections along a relation arrow

Rebasing is a bijection on the entire type of original sections, not just
on a finite chosen tuple. It commutes with arbitrary changes of test and
with composition of original arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.EquivalenceRelationFiber
variable {C : Type*} [Category* C] {D A T : C} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- All original relation sections with the specified first endpoint. -/
abbrev Sections (b : T ⟶ A) := {r : T ⟶ D // r ≫ p = b}

/-- Transport every section to the second endpoint of an original arrow. -/
def sectionRebase (a : T ⟶ D) : Sections (p := p) (a ≫ p) ≃
    Sections (p := p) (a ≫ q) where
  toFun r := ⟨compose e (a ≫ e.s) r.val (by
    rw [Category.assoc, e.symmetry₂, r.property]), by
      rw [compose_fst, Category.assoc, e.symmetry₁]⟩
  invFun r := ⟨compose e a r.val r.property.symm, compose_fst e _ _ _⟩
  left_inv r := by
    apply Subtype.ext
    apply e.right_cancellation
    · simp only [compose_fst, r.property]
    · simp only [compose_snd]
  right_inv r := by
    apply Subtype.ext
    apply e.right_cancellation
    · simp only [compose_fst, Category.assoc, e.symmetry₁, r.property]
    · simp only [compose_snd]

/-- Transport keeps the original second endpoint. -/
@[reassoc (attr := simp)] theorem sectionRebase_second (a : T ⟶ D)
    (r : Sections (p := p) (a ≫ p)) :
    (sectionRebase e a r).val ≫ q = r.val ≫ q := compose_snd e _ _ _

/-- Pull a section back along any further test morphism. -/
def sectionPull {U : C} (t : U ⟶ T) {b : T ⟶ A} (r : Sections (p := p) b) :
    Sections (p := p) (t ≫ b) :=
  ⟨t ≫ r.val, by rw [Category.assoc, r.property]⟩

/-- Rebasing agrees with arbitrary test change as an actual original arrow. -/
theorem sectionRebase_natural {U : C} (t : U ⟶ T) (a : T ⟶ D)
    (r : Sections (p := p) (a ≫ p)) :
    (sectionRebase e (t ≫ a)
      ⟨t ≫ r.val, by rw [Category.assoc, r.property, Category.assoc]⟩).val =
        t ≫ (sectionRebase e a r).val := by
  apply e.right_cancellation
  · simp only [Category.assoc, (sectionRebase e (t ≫ a) _).property,
      (sectionRebase e a r).property]
  · simp only [Category.assoc, sectionRebase_second]

include e in
/-- Two original arrows with the same first endpoint agree if their second endpoints do. -/
theorem sections_ext {b : T ⟶ A} {r s : Sections (p := p) b}
    (h : r.val ≫ q = s.val ≫ q) : r = s :=
  Subtype.ext (e.right_cancellation _ _ (r.property.trans s.property.symm) h)

/-- Rebase successively or along the composite: the resulting original arrow is identical. -/
theorem sectionRebase_comp (a b : T ⟶ D) (h : a ≫ q = b ≫ p)
    (r : Sections (p := p) (a ≫ p)) :
    (sectionRebase e b
      ⟨(sectionRebase e a r).val, (sectionRebase e a r).property.trans h⟩).val =
        (sectionRebase e (compose e a b h)
          ⟨r.val, r.property.trans (compose_fst e a b h).symm⟩).val := by
  apply e.right_cancellation
  · rw [(sectionRebase e b _).property,
      (sectionRebase e (compose e a b h) _).property, compose_snd]
  · simp only [sectionRebase_second]

/-- Rebasing along the identity original arrow leaves every original section unchanged. -/
theorem sectionRebase_identity (b : T ⟶ A) (r : Sections (p := p) b) :
    (sectionRebase e (b ≫ e.r)
      ⟨r.val, by rw [Category.assoc, e.reflexivity₁, Category.comp_id]; exact r.property⟩).val =
        r.val := by
  apply e.right_cancellation
  · rw [(sectionRebase e (b ≫ e.r) _).property, Category.assoc,
      e.reflexivity₂, Category.comp_id, r.property]
  · exact sectionRebase_second e _ _

end FLT.Mazur.EquivalenceRelationFiber
