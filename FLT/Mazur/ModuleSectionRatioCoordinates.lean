/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioPullback
public import FLT.Mazur.ModuleSectionIsomorphismTransport

/-!
# Computing pulled-back ratios from linear coordinates

Write sections in the basis given by the inverse image of one. A coordinate
multiplication identity then computes the genuine pulled-back section ratio.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}

/-- Linear coordinates compute the actual ratio after arbitrary pullback. -/
lemma sectionRatio_pullGlobal_of_coordinate (f : X ⟶ Y) (M : Y.Modules)
    (c : Γ(M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤)) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))]
    (r : Γ(X, ⊤)) (hr : r * f.appTop (c s) = f.appTop (c t)) :
    sectionRatio _ (pullGlobal f M s) (pullGlobal f M t) = r := by
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  have hc (v : Γ(M, ⊤)) : (c v) • c.symm 1 = v := by
    apply c.injective
    simp
  conv_lhs => rw [← hc s]
  conv_rhs => rw [← hc t]
  rw [map_smulₛₗ, map_smulₛₗ, smul_smul, hr]

/-- Composing scheme pullbacks preserves the actual section ratio. -/
lemma sectionRatio_comp_pullGlobal (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f _ (pullGlobal g M s)))] :
    let := globalSectionHom_isIso_comp_pullGlobal f g M s
    sectionRatio _ (pullGlobal (f ≫ g) M s) (pullGlobal (f ≫ g) M t) =
      sectionRatio _ (pullGlobal f _ (pullGlobal g M s))
        (pullGlobal f _ (pullGlobal g M t)) := by
  let := globalSectionHom_isIso_comp_pullGlobal f g M s
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  rw [← pullGlobal_comp_hom f g M s, ← pullGlobal_comp_hom f g M t,
    ← Hom.app_smul, sectionRatio_smul]

/-- A pulled-back sheaf comparison preserves ratios of compared sections. -/
lemma sectionRatio_pullGlobal_transport (f : X ⟶ Y) {M N : Y.Modules}
    (e : M ≅ N) (s t : Γ(M, ⊤))
    [IsIso (globalSectionHom _ (pullGlobal f M s))]
    [IsIso (globalSectionHom _ (pullGlobal f N (e.hom.app ⊤ s)))] :
    sectionRatio _ (pullGlobal f M s) (pullGlobal f M t) =
      sectionRatio _ (pullGlobal f N (e.hom.app ⊤ s))
        (pullGlobal f N (e.hom.app ⊤ t)) := by
  apply (sectionRatio_eq_iff _ _ _ _).mpr
  apply (ConcreteCategory.bijective_of_isIso (((pullback f).map e.hom).app ⊤)).injective
  rw [Hom.app_smul, pullGlobal_naturality, pullGlobal_naturality, sectionRatio_smul]

end FLT.Mazur.FCurve
