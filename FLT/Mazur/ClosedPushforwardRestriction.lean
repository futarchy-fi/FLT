/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionModulePushforward

/-!
# Open restriction of module pushforward

The open restriction square gives a natural comparison for actual module
sheaves. Its components are the section identifications induced by equality
of the corresponding opens, with their structure-sheaf actions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- Open restriction commutes naturally with pushforward of module sheaves. -/
def closedPushforwardRestriction :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
  have : (U.ι.opensFunctor ⋙ Opens.map f.base).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Y) _
  have : (Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (f ⁻¹ᵁ U).toScheme) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · exact NatIso.ofComponents
      (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V)) (by cat_disch)
  · ext V x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    change (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op)
      ((f.app (U.ι ''ᵁ V.unop)) x) = ((f ∣_ U).app V.unop) x
    exact congr($(morphismRestrict_app f U V.unop) x).symm

/-- The comparison on sections is restriction along the equality of inverse-image opens. -/
lemma closedPushforwardRestriction_hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    ((closedPushforwardRestriction f U).hom.app M).app V =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  rfl

/-- The inverse comparison on sections uses the reverse equality of opens. -/
lemma closedPushforwardRestriction_inv_app (M : X.Modules) (V : U.toScheme.Opens) :
    ((closedPushforwardRestriction f U).inv.app M).app V =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op := by
  rfl

/-- The comparison intertwines the actual structure-sheaf actions. -/
lemma closedPushforwardRestriction_hom_smul (M : X.Modules) (V : U.toScheme.Opens)
    (r : Γ(U.toScheme, V)) (m : Γ(((pushforward f).obj M).restrict U.ι, V)) :
    (((closedPushforwardRestriction f U).hom.app M).app V).hom (r • m) =
      r • (((closedPushforwardRestriction f U).hom.app M).app V).hom m :=
  Hom.app_smul _ _ _

/-- The inverse comparison also intertwines the structure-sheaf actions. -/
lemma closedPushforwardRestriction_inv_smul (M : X.Modules) (V : U.toScheme.Opens)
    (r : Γ(U.toScheme, V))
    (m : Γ((pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V)) :
    (((closedPushforwardRestriction f U).inv.app M).app V).hom (r • m) =
      r • (((closedPushforwardRestriction f U).inv.app M).app V).hom m :=
  Hom.app_smul _ _ _

end FLT.Mazur.FCurve.CoherentDevissage
