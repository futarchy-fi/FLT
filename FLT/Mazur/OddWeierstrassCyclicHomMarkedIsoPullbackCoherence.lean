/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedIsoParameterTransport

/-!
# Identity and composition coherence for specified marked pullbacks

The specified comparisons satisfy identity and iterated-source-change laws
after explicit equality transport of the original parameter expressions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g))
  (ha : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
    e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)

include ha in
/-- Identity source change recovers the specified original comparison. -/
theorem cyclicHomMarkedIsoPullback_id :
    cyclicHomMarkedIsoTransport n (𝟙 T ≫ f) (𝟙 T ≫ g) f g
      (Category.id_comp f).symm (Category.id_comp g).symm
      (cyclicHomMarkedIsoPullback n f g e (𝟙 T)) = e := by
  apply cyclicHomMarkedGroupIso_unique n f g _ e _ ha
  exact cyclicHomMarkedIsoTransport_auxiliary n _ _ _ _ _ _ _
    (cyclicHomMarkedIsoPullback_auxiliary n f g e (𝟙 T) ha)

include ha in
/-- Iterated source change agrees with source change along the composite. -/
theorem cyclicHomMarkedIsoPullback_comp {U V : Scheme} (k : U ⟶ T) (l : V ⟶ U) :
    cyclicHomMarkedIsoTransport n (l ≫ (k ≫ f)) (l ≫ (k ≫ g))
      ((l ≫ k) ≫ f) ((l ≫ k) ≫ g) (Category.assoc l k f) (Category.assoc l k g)
      (cyclicHomMarkedIsoPullback n (k ≫ f) (k ≫ g)
        (cyclicHomMarkedIsoPullback n f g e k) l) =
      cyclicHomMarkedIsoPullback n f g e (l ≫ k) := by
  apply cyclicHomMarkedGroupIso_unique n ((l ≫ k) ≫ f) ((l ≫ k) ≫ g)
  · exact cyclicHomMarkedIsoTransport_auxiliary n _ _ _ _ _ _ _
      (cyclicHomMarkedIsoPullback_auxiliary n (k ≫ f) (k ≫ g) _ l
        (cyclicHomMarkedIsoPullback_auxiliary n f g e k ha))
  · exact cyclicHomMarkedIsoPullback_auxiliary n f g e (l ≫ k) ha

/-- Pullback carries the identity group comparison to the actual new-source identity. -/
theorem cyclicHomMarkedIsoPullback_refl {U : Scheme} (k : U ⟶ T) :
    cyclicHomMarkedIsoPullback n f f (Iso.refl _) k = Iso.refl _ := by
  apply cyclicHomMarkedGroupIso_eq_refl
  exact cyclicHomMarkedIsoPullback_auxiliary n f f (Iso.refl _) k
    (fun _ ↦ Category.comp_id _)

/-- Pullback of comparisons respects their actual composition before imposing marking equations. -/
theorem cyclicHomMarkedIsoPullback_trans {U : Scheme} (k : U ⟶ T)
    (p : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (d : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n p)) :
    cyclicHomMarkedIsoPullback n f p (e ≪≫ d) k =
      cyclicHomMarkedIsoPullback n f g e k ≪≫ cyclicHomMarkedIsoPullback n g p d k := by
  apply Iso.ext
  simp only [cyclicHomMarkedIsoPullback_def, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.OddWeierstrassParameter
