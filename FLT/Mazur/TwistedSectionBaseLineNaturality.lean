/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSourceNaturality
public import FLT.Mazur.TwistedSectionPushforward

/-!
# The direct-image correspondence retains base-line transport

An actual base-line isomorphism induces the expected tensor map on original
sections and the contravariant dual map on their direct-image morphisms.
The comparison uses canonical pullback duality and the sheaf adjunction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{u}}

/-- Inverse tensor duality retains transport of the original twisting line. -/
lemma lineHomSectionEquiv_symm_sourceIso {B C : X.Modules} (e : B ≅ C)
    (L : X.Modules) (hB : LocallyFreeRankOne B) (hC : LocallyFreeRankOne C)
    (s : Γ(tensor L B, ⊤)) :
    (lineHomSectionEquiv L hC).symm ((map (𝟙 L) e.hom).app ⊤ s) =
      moduleSheafDualMap B e.hom ≫ (lineHomSectionEquiv L hB).symm s := by
  apply (lineHomSectionEquiv L hC).injective
  rw [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply, moduleSheafDualIso] using
    (lineHomSectionEquiv_sourceIso e L hB hC ((lineHomSectionEquiv L hB).symm s)).symm

/-- A base-line isomorphism acts by its actual dual on the original direct-image map. -/
lemma twistedSectionPushforwardEquiv_baseLineIso (f : X ⟶ S) (L : X.Modules)
    {B C : S.Modules} (e : B ≅ C) (hB : LocallyFreeRankOne B)
    (hC : LocallyFreeRankOne C) (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    twistedSectionPushforwardEquiv f L hC
        ((map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s) =
      moduleSheafDualMap B e.hom ≫ twistedSectionPushforwardEquiv f L hB s := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
  rw [twistedSectionPushforwardEquiv_adjoint, Adjunction.homEquiv_naturality_left_symm,
    twistedSectionPushforwardEquiv_adjoint]
  have h := lineHomSectionEquiv_symm_sourceIso ((pullback f).mapIso e) L
    (hB.pullback f) (hC.pullback f) s
  simp only [Functor.mapIso_hom] at h
  rw [h]
  simp only [moduleSheafDualPullbackIso_hom]
  rw [← Category.assoc, ← moduleSheafDualPullbackHom_naturality, Category.assoc]

end FLT.Mazur.FCurve
