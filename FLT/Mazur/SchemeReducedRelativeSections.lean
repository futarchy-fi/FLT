/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeConnectedFiberSections
public import FLT.Mazur.SchemeReducedSectionDetection

/-!
# Relative constant functions for a reduced total space

For a pointed proper family with geometrically connected reduced fibers and a
reduced total space, pullback of global functions is an isomorphism. Its inverse
is evaluation along the section. Equality is proved on all residue-field points;
no relative cohomology comparison is taken as an input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeReducedRelativeSections
variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f] [IsReduced X]

include hs in
/-- Evaluation along the section followed by pullback fixes every global function. -/
lemma section_appTop_comp : s.appTop ≫ f.appTop = 𝟙 Γ(X, ⊤) := by
  apply SchemeReducedSectionDetection.hom_ext
  intro x
  have hpoint : (X.fromSpecResidueField x ≫ f ≫ s) ≫ f =
      X.fromSpecResidueField x ≫ f := by
    simp only [Category.assoc, hs, Category.comp_id]
  have h := SchemeConnectedFiberSections.appTop_eq_of_same_fiber f
    (X.fromSpecResidueField x ≫ f ≫ s) (X.fromSpecResidueField x) hpoint
  change (X.fromSpecResidueField x ≫ f ≫ s).appTop =
    (X.fromSpecResidueField x).appTop at h
  simpa only [Scheme.Hom.comp_appTop, Category.assoc, Category.id_comp] using h

/-- The original pullback of functions is inverted by the original section evaluation. -/
def sectionsIso : Γ(S, ⊤) ≅ Γ(X, ⊤) where
  hom := f.appTop
  inv := s.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  inv_hom_id := section_appTop_comp f s hs

/-- The relative comparison retains the specified structural pullback. -/
lemma sectionsIso_hom : (sectionsIso f s hs).hom = f.appTop := rfl

/-- The relative inverse retains evaluation at the specified section. -/
lemma sectionsIso_inv : (sectionsIso f s hs).inv = s.appTop := rfl

include s hs in
/-- The actual structural map on global functions is bijective. -/
lemma appTop_bijective : Function.Bijective f.appTop :=
  (ConcreteCategory.bijective_of_isIso (sectionsIso f s hs).hom)

include hs in
/-- Sections give the same global evaluation, although the scheme sections may differ. -/
lemma section_evaluation_independent (t : S ⟶ X) (ht : t ≫ f = 𝟙 S) :
    s.appTop = t.appTop := by
  let _ : IsIso f.appTop := (sectionsIso f s hs).isIso_hom
  rw [← cancel_epi f.appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hs, ht]

end FLT.Mazur.SchemeReducedRelativeSections
