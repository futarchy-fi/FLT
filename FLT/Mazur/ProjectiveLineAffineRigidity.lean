/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineConstantSections
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# Maps from the projective line to affine schemes are constant

The original structure morphism identifies global functions with the coefficient
field. Evaluation at either original endpoint therefore determines every map
into an affine scheme, including maps obtained by factoring through an affine open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProjectiveLineAffineRigidity
open ProjectiveLine FCurve
universe u
variable (K : Type u) [Field K]

/-- The specified projective-line structure map is an isomorphism on global functions. -/
theorem appTop_isIso : IsIso (toBase K).appTop := by
  have h := ProjectiveLineConstantSections.constant_sections K
  have hb : Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ (toBase K).appTop) := h
  have hi := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  let _ := hi
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv (toBase K).appTop

/-- Evaluation at any original section is inverse to the global-functions pullback. -/
theorem section_appTop (s : Spec (.of K) ⟶ scheme K) (hs : s ≫ toBase K = 𝟙 _) :
    s.appTop ≫ (toBase K).appTop = 𝟙 _ := by
  let _ := appTop_isIso K
  apply (cancel_epi (toBase K).appTop).mp
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop,
    Category.id_comp, Category.comp_id]

/-- An affine-target morphism equals its original endpoint value on the whole line. -/
theorem eq_constant {Y : Scheme.{u}} [IsAffine Y] (f : scheme K ⟶ Y) :
    f = toBase K ≫ zero K ≫ f := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc,
    section_appTop K (zero K) (zero_toBase K), Category.comp_id]

/-- Factoring through an affine scheme suffices for constancy in an arbitrary target. -/
theorem comp_eq_constant {Y Z : Scheme.{u}} [IsAffine Y]
    (f : scheme K ⟶ Y) (j : Y ⟶ Z) :
    f ≫ j = toBase K ≫ zero K ≫ f ≫ j := by
  conv_lhs => rw [eq_constant K f]
  simp only [Category.assoc]

/-- The two original endpoints have equal images under any affine-target map. -/
theorem endpoints_eq {Y : Scheme.{u}} [IsAffine Y] (f : scheme K ⟶ Y) :
    zero K ≫ f = infinity K ≫ f := by
  conv_rhs => rw [eq_constant K f]
  rw [infinity_toBase_assoc]

end FLT.Mazur.ProjectiveLineAffineRigidity
