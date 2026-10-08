/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonBaseCover

/-!
# Sections of the constructed common cover

Two lifts of an affine base test into the original covering charts construct
a section of their common cover. Its two projections retain the prescribed
lifts, using only the universal properties of the ring pushouts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A)
variable (b : C.coverRing ⟶ A) (hb : C.ringMap ≫ b = f)

/-- A lift into the original covering chart splits its base-changed cover. -/
def baseChangeSection : (C.baseChange f).coverRing ⟶ A :=
  pushout.desc (𝟙 A) b (by simpa only [Category.comp_id] using hb.symm)

/-- The constructed section is over its given affine base. -/
@[reassoc]
lemma baseChangeSection_base :
    (C.baseChange f).ringMap ≫ C.baseChangeSection f b hb = 𝟙 A :=
  pushout.inl_desc _ _ _

/-- The section retains the original covering-chart lift. -/
@[reassoc]
lemma baseChangeSection_cover :
    (C.baseChangeRefinement f).cover ≫ C.baseChangeSection f b hb = b :=
  pushout.inr_desc _ _ _

variable (C' : Chart p) (g : C'.baseRing ⟶ A)
variable (c : C'.coverRing ⟶ A) (hc : C'.ringMap ≫ c = g)

/-- Independent covering-chart lifts construct a section of the common cover. -/
def commonCoverSection : C.commonCoverRing C' f g ⟶ A :=
  pushout.desc (C.baseChangeSection f b hb) (C'.baseChangeSection g c hc)
    ((C.baseChangeSection_base f b hb).trans (C'.baseChangeSection_base g c hc).symm)

/-- The common-cover section retains the first prescribed lift. -/
@[reassoc]
lemma commonCoverSection_left :
    C.commonCoverLeft C' f g ≫ C.commonCoverSection f b hb C' g c hc = b := by
  simp only [commonCoverLeft, commonCoverSection, Category.assoc, pushout.inl_desc,
    baseChangeSection_cover]

/-- The common-cover section retains the second prescribed lift. -/
@[reassoc]
lemma commonCoverSection_right :
    C.commonCoverRight C' f g ≫ C.commonCoverSection f b hb C' g c hc = c := by
  simp only [commonCoverRight, commonCoverSection, Category.assoc, pushout.inr_desc,
    baseChangeSection_cover]

/-- The constructed common-cover map is split by the two prescribed lifts. -/
@[reassoc]
lemma commonCoverMap_section :
    C.commonCoverMap C' f g ≫ C.commonCoverSection f b hb C' g c hc = 𝟙 A := by
  simp only [commonCoverMap, commonCoverSection, Category.assoc, pushout.inl_desc,
    baseChangeSection_base]

/-- On spectra the common-cover section retains the first original covering coordinate. -/
@[reassoc]
lemma commonCoverSection_spec_left :
    Spec.map (C.commonCoverSection f b hb C' g c hc) ≫
        Spec.map (C.commonCoverLeft C' f g) = Spec.map b := by
  rw [← Spec.map_comp, commonCoverSection_left]

/-- On spectra the common-cover section retains the second original covering coordinate. -/
@[reassoc]
lemma commonCoverSection_spec_right :
    Spec.map (C.commonCoverSection f b hb C' g c hc) ≫
        Spec.map (C.commonCoverRight C' f g) = Spec.map c := by
  rw [← Spec.map_comp, commonCoverSection_right]

/-- The section on spectra splits the actual faithfully flat common cover. -/
@[reassoc]
lemma commonCoverSection_spec_base :
    Spec.map (C.commonCoverSection f b hb C' g c hc) ≫
        Spec.map (C.commonCoverMap C' f g) = 𝟙 (Spec A) := by
  rw [← Spec.map_comp, commonCoverMap_section, Spec.map_id]

end FLT.Mazur.SchemeAffineDescent.Chart
