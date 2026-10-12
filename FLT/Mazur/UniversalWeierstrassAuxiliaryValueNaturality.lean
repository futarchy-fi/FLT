/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryGroupSourceNaturality

/-!
# Normalization of arbitrary universal-family values is natural

Any section over an auxiliary frame can be normalized by the actual entire
group comparison. This applies to labels outside the auxiliary marking too.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme} (f : T ⟶ levelFour.left) (s : T ⟶ universalGroup.left)
  (hs : s ≫ universalGroup.hom = f ≫ levelFour.hom)

/-- The normalized universal value of an arbitrary section over the original frame. -/
def auxiliarySchemeNormalizedValue : T ⟶ universalGroup.left :=
  pullback.lift s (𝟙 T) (hs.trans (Category.id_comp _).symm) ≫
    (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (auxiliarySchemeNormalizedPoint f ≫ levelFour.hom)

/-- Normalization of every actual value commutes with every source morphism. -/
theorem auxiliarySchemeNormalizedValue_natural (k : U ⟶ T)
    (hs' : (k ≫ s) ≫ universalGroup.hom = (k ≫ f) ≫ levelFour.hom) :
    auxiliarySchemeNormalizedValue (k ≫ f) (k ≫ s) hs' =
      k ≫ auxiliarySchemeNormalizedValue f s hs := by
  have hl : pullback.lift (k ≫ s) (𝟙 U) (hs'.trans (Category.id_comp _).symm) ≫
      auxiliarySchemeOriginalSourceMap f k =
    k ≫ pullback.lift s (𝟙 T) (hs.trans (Category.id_comp _).symm) := by
    apply pullback.hom_ext
    · change (_ ≫ _) ≫ pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
        (_ ≫ _) ≫ pullback.fst universalGroup.hom (f ≫ levelFour.hom)
      rw [Category.assoc, auxiliarySchemeOriginalSourceMap_fst, pullback.lift_fst,
        Category.assoc, pullback.lift_fst]
    · have hm : auxiliarySchemeOriginalSourceMap f k ≫
          pullback.snd universalGroup.hom (f ≫ levelFour.hom) =
        pullback.snd universalGroup.hom ((k ≫ f) ≫ levelFour.hom) ≫ k :=
        auxiliarySchemeOriginalSourceMap_snd f k
      change (_ ≫ _) ≫ pullback.snd universalGroup.hom (f ≫ levelFour.hom) =
        (_ ≫ _) ≫ pullback.snd universalGroup.hom (f ≫ levelFour.hom)
      rw [Category.assoc, hm, pullback.lift_snd_assoc, Category.id_comp, Category.assoc,
        pullback.lift_snd, Category.comp_id]
  unfold auxiliarySchemeNormalizedValue
  rw [← auxiliarySchemeNormalizedSourceMap_fst f k,
    ← auxiliarySchemeNormalizationGroupIso_inv_natural_assoc, ← Category.assoc,
    hl, Category.assoc]

/-- Equal original frames and values retain the same natural normalization comparison. -/
theorem auxiliarySchemeNormalizedValue_natural_of_eq (k : U ⟶ T)
    (f' : U ⟶ levelFour.left) (s' : U ⟶ universalGroup.left)
    (hs' : s' ≫ universalGroup.hom = f' ≫ levelFour.hom)
    (hf : f' = k ≫ f) (he : s' = k ≫ s) :
    auxiliarySchemeNormalizedValue f' s' hs' = k ≫ auxiliarySchemeNormalizedValue f s hs := by
  subst f'
  subst s'
  exact auxiliarySchemeNormalizedValue_natural f s hs k hs'

end FLT.Mazur.UniversalWeierstrass
