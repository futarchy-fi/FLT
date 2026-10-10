/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianProperEvaluation

/-!
# Relative functions over a possibly nonreduced Noetherian affine base

Structural pullback is an isomorphism for a pointed flat proper family with
geometrically connected reduced fibers. The inverse is the original section
map, with no reducedness hypothesis on the base or the total space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NoetherianProperRelativeFunctions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Structural pullback is bijective over the spectrum of any Noetherian ring. -/
theorem spec_appTop_bijective {R : CommRingCat.{0}} [IsNoetherianRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Flat f]
    [GeometricallyConnected f] [GeometricallyReduced f]
    (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _) : Function.Bijective f.appTop :=
  ⟨Function.LeftInverse.injective
    (SchemeRelativeNilpotentSections.evaluation_pullback f s hs),
    fun x ↦ ⟨s.appTop x, NoetherianProperEvaluation.pullback_evaluation f s hs x⟩⟩

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs in
/-- The actual global-functions comparison for any Noetherian affine base. -/
theorem appTop_bijective : Function.Bijective f.appTop := by
  let _ : GeometricallyConnected (f ≫ S.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ ‹GeometricallyConnected f›
  let _ : GeometricallyReduced (f ≫ S.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ ‹GeometricallyReduced f›
  have H := spec_appTop_bijective (f ≫ S.isoSpec.hom) (S.isoSpec.inv ≫ s) (by
    simp only [Category.assoc, ← Category.assoc s f, hs, Category.id_comp, Iso.inv_hom_id])
  have hi : IsIso (f ≫ S.isoSpec.hom).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr H
  rw [Scheme.Hom.comp_appTop, isIso_comp_left_iff] at hi
  exact (ConcreteCategory.isIso_iff_bijective _).mp hi

/-- Actual functions are precisely scalars from the original base. -/
def sectionsIso : Γ(S, ⊤) ≅ Γ(X, ⊤) :=
  (RingEquiv.ofBijective f.appTop.hom (appTop_bijective f s hs)).toCommRingCatIso

/-- The comparison uses the original structure morphism. -/
lemma sectionsIso_hom : (sectionsIso f s hs).hom = f.appTop := rfl

/-- Its inverse is evaluation along the given section. -/
lemma sectionsIso_inv : (sectionsIso f s hs).inv = s.appTop := by
  apply (cancel_epi (sectionsIso f s hs).hom).mp
  rw [Iso.hom_inv_id, sectionsIso_hom, ← Scheme.Hom.comp_appTop, hs,
    Scheme.Hom.id_appTop]

end FLT.Mazur.NoetherianProperRelativeFunctions
