/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSectionEquiv

/-!
# Twisted sections and the actual direct image

Tensor duality, canonical pullback of the dual line, and the sheaf adjunction
identify twisted sections with morphisms into the actual direct image.
No properness or cohomological vanishing is needed for this correspondence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
variable {B : S.Modules} (hB : LocallyFreeRankOne B)

/-- Actual twisted sections correspond to maps from the dual base line to the direct image. -/
def twistedSectionPushforwardEquiv :
    Γ(tensor L ((pullback f).obj B), ⊤) ≃
      (moduleSheafDual B ⟶ (pushforward f).obj L) :=
  (lineHomSectionEquiv L (hB.pullback f)).symm.trans
    ((Iso.homCongr (moduleSheafDualPullbackIso f hB).symm (Iso.refl L)).trans
      ((pullbackPushforwardAdjunction f).homEquiv _ _))

/-- Taking the adjoint retains the canonical dual pullback comparison. -/
lemma twistedSectionPushforwardEquiv_adjoint
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
        (twistedSectionPushforwardEquiv f L hB s) =
      (moduleSheafDualPullbackIso f hB).hom ≫
        (lineHomSectionEquiv L (hB.pullback f)).symm s := by
  simp only [twistedSectionPushforwardEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]

/-- The section recovered from a direct-image map has the original adjoint on the total space. -/
lemma twistedSectionPushforwardEquiv_symm_adjoint
    (a : moduleSheafDual B ⟶ (pushforward f).obj L) :
    (moduleSheafDualPullbackIso f hB).hom ≫
        (lineHomSectionEquiv L (hB.pullback f)).symm
          ((twistedSectionPushforwardEquiv f L hB).symm a) =
      ((pullbackPushforwardAdjunction f).homEquiv _ _).symm a := by
  rw [← twistedSectionPushforwardEquiv_adjoint, Equiv.apply_symm_apply]

/-- The counit description of the recovered map gives a concrete normalization diagram. -/
lemma twistedSectionPushforwardEquiv_counit
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    (pullback f).map (twistedSectionPushforwardEquiv f L hB s) ≫
        (pullbackPushforwardAdjunction f).counit.app L =
      (moduleSheafDualPullbackIso f hB).hom ≫
        (lineHomSectionEquiv L (hB.pullback f)).symm s :=
  twistedSectionPushforwardEquiv_adjoint f L hB s

end FLT.Mazur.FCurve
