/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOriginalReconstructionTransport
public import FLT.Mazur.SchemeAffineCoverTestOriginalMap

/-!
# Covering recovery intertwines original descent transport

Normalize the two base paths separately. Original chart reconstruction
then proves compatibility with transport between independent source lifts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso coverRecoveryIso

/-- Normalized covering recovery intertwines original transport over a common base test. -/
lemma coverRecoveryIso_affine_transport_of_square (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f)
    (hg : Spec.map c ≫ Spec.map (C j).ringMap = Spec.map g)
    (hz : (Spec.map b ≫ (C i).cover) ≫ p = Spec.map f ≫ (C i).base)
    (hz' : (Spec.map c ≫ (C j).cover) ≫ p = Spec.map f ≫ (C i).base) :
    (comparison (Spec.map b ≫ (C i).cover) p
        (Spec.map f ≫ (C i).base) hz).inv.app (openGlued C D) ≫
        normalize (Spec.map b) (C i).cover (C i).cover
          (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) rfl rfl
          (coverRecoveryIso C D i).hom ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (hz.trans hz'.symm)).hom =
      (comparison (Spec.map c ≫ (C j).cover) p
        (Spec.map f ≫ (C i).base) hz').inv.app (openGlued C D) ≫
        normalize (Spec.map c) (C j).cover (C j).cover
          (Spec.map c ≫ (C j).cover) (Spec.map c ≫ (C j).cover) rfl rfl
          (coverRecoveryIso C D j).hom := by
  rw [coverRecoveryIso_test_originalMap C D i f b ha _ _ rfl hz rfl,
    coverRecoveryIso_test_originalMap C D j g c hg _ _ rfl hz' w.symm]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact chartTestRecoveryIso_originalMaps_transport_of_square C D i j f g b c hb hc w ha hg

end FLT.Mazur.SchemeAffineDescent
