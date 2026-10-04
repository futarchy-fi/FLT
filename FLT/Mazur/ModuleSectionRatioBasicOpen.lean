/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Ratios identify intersections of generator opens

A numerator generates exactly where its ratio to an existing generator is a
unit. Thus the ratio's scheme basic open is the intersection of the two actual
nonvanishing opens, including non-rational points.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules) (s t : Γ(M, ⊤))

/-- A unit ratio certifies generation by its numerator on the entire open. -/
lemma le_sectionGeneratorOpen_of_ratio_isUnit (U : X.Opens)
    (hs : U ≤ sectionGeneratorOpen M s) (ht : IsUnit (sectionRatioOn M s U hs t)) :
    U ≤ sectionGeneratorOpen M t := by
  apply (le_moduleHomIsoOpen_iff _ U).mpr
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := U.ι_image_le V
  have := sectionGeneratorOpen_app_isIso M s W (hWU.trans hs)
  have hr : IsUnit (sectionRatioOn M s W (hWU.trans hs) t) := by
    rw [← sectionRatioOn_restrict M s U W hs hWU]
    exact ht.map (X.presheaf.map (homOfLE hWU).op).hom
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun a : Γ(X, W) ↦ (globalSectionHom M t).app W a)
  have he : (fun a : Γ(X, W) ↦ (globalSectionHom M t).app W a) =
      fun a ↦ (globalSectionHom M s).app W (a * sectionRatioOn M s W (hWU.trans hs) t) := by
    funext a
    change a • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op t =
      (a * sectionRatioOn M s W (hWU.trans hs) t) •
        M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s
    rw [mul_smul, sectionRatioOn_smul]
  rw [he]
  obtain ⟨v, hv⟩ := hr
  rw [← hv]
  exact (ConcreteCategory.bijective_of_isIso ((globalSectionHom M s).app W)).comp
    (Units.mulRight v).bijective

/-- The numerator generates on the ratio's basic open. -/
lemma sectionRatioOn_basicOpen_le (U : X.Opens) (hs : U ≤ sectionGeneratorOpen M s) :
    X.basicOpen (sectionRatioOn M s U hs t) ≤ sectionGeneratorOpen M t := by
  let W := X.basicOpen (sectionRatioOn M s U hs t)
  have hWU : W ≤ U := X.basicOpen_le _
  apply le_sectionGeneratorOpen_of_ratio_isUnit M s t W (hWU.trans hs)
  rw [← sectionRatioOn_restrict M s U W hs hWU]
  exact X.toRingedSpace.isUnit_res_basicOpen _

/-- Ratio basic opens are precisely the intersections of actual nonvanishing opens. -/
lemma sectionRatioOn_basicOpen (U : X.Opens) (hs : U ≤ sectionGeneratorOpen M s) :
    X.basicOpen (sectionRatioOn M s U hs t) = U ⊓ sectionGeneratorOpen M t := by
  apply le_antisymm
  · exact le_inf (X.basicOpen_le _) (sectionRatioOn_basicOpen_le M s t U hs)
  · let V := U ⊓ sectionGeneratorOpen M t
    have hv : IsUnit (sectionRatioOn M s V (inf_le_left.trans hs) t) :=
      sectionRatioOn_isUnit M s t V (inf_le_left.trans hs) inf_le_right
    have he := X.basicOpen_of_isUnit hv
    rw [← sectionRatioOn_restrict M s U V hs inf_le_left, X.basicOpen_res] at he
    exact inf_eq_left.mp he

end FLT.Mazur.FCurve
