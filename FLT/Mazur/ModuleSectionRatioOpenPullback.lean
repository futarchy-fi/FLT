/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen
public import FLT.Mazur.ModuleSectionRatioPullback

/-!
# Pulling local section ratios to an open chart

The ratio on the image of an open immersion becomes the ratio of the genuine
pulled-back sections under the structure-sheaf section isomorphism.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- Pullback of a local ratio to its open chart agrees with the actual section ratio. -/
lemma sectionRatioOn_openPullback (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))]
    (hf : f ''ᵁ ⊤ ≤ sectionGeneratorOpen M s) :
    (f.appIso ⊤).hom (sectionRatioOn M s (f ''ᵁ ⊤) hf t) =
      sectionRatio _ (pullGlobal f M s) (pullGlobal f M t) := by
  symm
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  rw [← pullGlobal_restrict f M s, ← pullGlobal_restrict f M t, ← Hom.app_smul]
  congr 1
  have he := sectionRatioOn_smul M s (f ''ᵁ ⊤) hf t
  apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).injective
  erw [M.smul_restrictAppIso_hom_apply f ⊤]
  change (f.appIso ⊤).inv ((f.appIso ⊤).hom (sectionRatioOn M s (f ''ᵁ ⊤) hf t)) •
    M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s =
      M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op t
  simpa only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] using he

end FLT.Mazur.FCurve
