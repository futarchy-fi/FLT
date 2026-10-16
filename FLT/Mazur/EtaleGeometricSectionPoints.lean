/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedSectionImmersion
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Geometric sections and points of the entire etale fiber

For an etale scheme over a separably closed field, evaluation identifies
all sections with all points. Uniqueness uses the actual open section,
so no reducedness or equality of morphisms from equality of images is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtaleGeometricSections
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of K)) [Etale p]

/-- All actual sections of the original etale scheme over the field. -/
abbrev Sections := {s : Spec (.of K) ⟶ X // s ≫ p = 𝟙 _}

/-- A section is determined by its point because its image is an actual open subscheme. -/
theorem section_ext {s t : Sections p} (h : s.val default = t.val default) : s = t := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion p s.val s.property
  have hr : Set.range t.val ⊆ Set.range s.val := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by simpa only [Subsingleton.elim x default] using h⟩
  let z := IsOpenImmersion.lift s.val t.val hr
  have hz : z ≫ s.val = t.val := IsOpenImmersion.lift_fac _ _ _
  have hi : z = 𝟙 _ := by
    calc
      z = z ≫ s.val ≫ p := by rw [s.property, Category.comp_id]
      _ = t.val ≫ p := by rw [← Category.assoc, hz]
      _ = 𝟙 _ := t.property
  apply Subtype.ext
  simpa only [hi, Category.id_comp] using hz

/-- Evaluation on sections is injective for any field, including nonsplit etale fibers. -/
theorem evaluation_injective : Function.Injective (fun s : Sections p ↦ s.val default) :=
  fun _ _ h ↦ section_ext p h

variable [IsSepClosed K]

/-- Every point of the entire etale scheme supplies a section over the original field. -/
theorem evaluation_surjective : Function.Surjective (fun s : Sections p ↦ s.val default) := by
  intro x
  obtain ⟨s, hs, hx⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p (𝟙 _) x
    (Subsingleton.elim _ _)
  exact ⟨⟨s, hs⟩, hx⟩

/-- The whole section type is equivalent to the whole geometric fiber, with no finiteness needed. -/
def sectionPointEquiv : Sections p ≃ X :=
  Equiv.ofBijective (fun s ↦ s.val default)
    ⟨evaluation_injective p, evaluation_surjective p⟩

omit [IsSepClosed K] in
/-- A pointwise complete list enumerates every actual section, not just its image. -/
theorem bijective_sections_of_evaluation {I : Type*} (s : I → Sections p)
    (h : Function.Bijective (fun i ↦ (s i).val default)) : Function.Bijective s := by
  constructor
  · intro i j hij
    exact h.1 (congrArg (fun z : Sections p ↦ z.val default) hij)
  · intro t
    obtain ⟨i, hi⟩ := h.2 (t.val default)
    exact ⟨i, section_ext p hi⟩

end FLT.Mazur.EtaleGeometricSections
