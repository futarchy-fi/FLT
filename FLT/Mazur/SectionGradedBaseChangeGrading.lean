/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedBaseChangeDegrees
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Internal grading of the scalar-extended section algebra

The structural homogeneous pieces form an internal grading. Scalar extension
preserves this grading without a flatness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings TensorProduct
namespace FLT.Mazur.SectionGradedBaseChange
open FCurve OpenModuleSectionScalars SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S T : Scheme} (f : X ⟶ S) (L : X.Modules) (g : T ⟶ S)

/-- Changing the structural scalar ring does not change homogeneous membership. -/
lemma mem_baseGrade_iff (n : ℕ) (s : sectionModule f L) :
    s ∈ baseGrade f L n ↔ s ∈ grade L ⊤ n := Iff.rfl

/-- The structural homogeneous pieces form an internal graded algebra. -/
instance baseGradedAlgebra : GradedAlgebra (baseGrade f L) :=
  { sectionGradedAlgebra L ⊤ with }

/-- The canonical internal grading after extending structural scalars. -/
def tensorGrade (n : ℕ) :
    Submodule Γ(T, ⊤) ((ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :=
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  (baseGrade f L n).baseChange Γ(T, ⊤)

/-- Internal scalar extension is a graded algebra, even for a nonflat base map. -/
instance tensorGradedAlgebra : GradedAlgebra (tensorGrade f L g) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact GradedAlgebra.baseChange (baseGrade f L)

/-- The internal tensor grading equals the previously used extended degree ranges. -/
lemma tensorGrade_eq_extendedGrade (n : ℕ) :
    tensorGrade f L g n = extendedGrade f L g n := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    induction s using TensorProduct.inductionOn with
    | tmul b s =>
      obtain ⟨s, t, rfl⟩ := s
      exact ⟨b ⊗ₜ[Γ(S, ⊤)] t, rfl⟩
    | add s t hs ht => simpa only [map_add] using Submodule.add_mem _ hs ht
  · rintro _ ⟨s, rfl⟩
    induction s using TensorProduct.inductionOn with
    | tmul b s =>
      exact ⟨b ⊗ₜ[Γ(S, ⊤)] ⟨baseOf f L n s, ⟨s, rfl⟩⟩, rfl⟩
    | add s t hs ht => simpa only [map_add] using Submodule.add_mem _ hs ht

/-- The original extended degree ranges themselves carry the full internal grading. -/
instance extendedGradedAlgebra : GradedAlgebra (extendedGrade f L g) := by
  rw [← funext (tensorGrade_eq_extendedGrade f L g)]
  infer_instance

/-- Structural scalar extension preserves each homogeneous element's degree. -/
lemma tmul_mem_extendedGrade (n : ℕ) (b : Γ(T, ⊤))
    {s : sectionModule f L} (hs : s ∈ baseGrade f L n) :
    b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s ∈ extendedGrade f L g n := by
  obtain ⟨s, rfl⟩ := hs
  exact ⟨b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s, rfl⟩

end FLT.Mazur.SectionGradedBaseChange
