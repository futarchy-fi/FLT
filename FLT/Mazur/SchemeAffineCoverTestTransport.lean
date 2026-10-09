/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCoverRecoveryTransport

/-!
# Covering transport on arbitrary affine source tests

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

/-- Original reconstruction intertwines transport between distinct source maps. -/
lemma chartTestRecoveryIso_originalMaps_transport_of_base (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (z : Spec A ⟶ X)
    (hf : Spec.map f ≫ (C i).base = z) (hf' : Spec.map g ≫ (C j).base = z)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f)
    (hg : Spec.map c ≫ Spec.map (C j).ringMap = Spec.map g) :
    (C i).sectionOriginalMap D f (Spec.map b) ha
        (Spec.map b ≫ (C i).cover) rfl
        (chartTestRecoveryIso C D i z (Spec.map f) hf).hom ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (((C i).cover_spec_over f b hb).trans
            (hf.trans (hf'.symm.trans ((C j).cover_spec_over g c hc).symm)))).hom =
      (C j).sectionOriginalMap D g (Spec.map c) hg
        (Spec.map c ≫ (C j).cover) rfl
        (chartTestRecoveryIso C D j
          z (Spec.map g) hf').hom := by
  subst z
  exact chartTestRecoveryIso_originalMaps_transport_of_square
    C D i j f g b c hb hc hf'.symm ha hg

/-- Normalized covering recovery intertwines original transport over a common base test. -/
lemma coverRecoveryIso_affine_transport_of_base (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (z : Spec A ⟶ X)
    (hf : Spec.map f ≫ (C i).base = z) (hf' : Spec.map g ≫ (C j).base = z)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f)
    (hg : Spec.map c ≫ Spec.map (C j).ringMap = Spec.map g)
    (hz : (Spec.map b ≫ (C i).cover) ≫ p = z)
    (hz' : (Spec.map c ≫ (C j).cover) ≫ p = z) :
    (comparison (Spec.map b ≫ (C i).cover) p
        z hz).inv.app (openGlued C D) ≫
        normalize (Spec.map b) (C i).cover (C i).cover
          (Spec.map b ≫ (C i).cover) (Spec.map b ≫ (C i).cover) rfl rfl
          (coverRecoveryIso C D i).hom ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (hz.trans hz'.symm)).hom =
      (comparison (Spec.map c ≫ (C j).cover) p
        z hz').inv.app (openGlued C D) ≫
        normalize (Spec.map c) (C j).cover (C j).cover
          (Spec.map c ≫ (C j).cover) (Spec.map c ≫ (C j).cover) rfl rfl
          (coverRecoveryIso C D j).hom := by
  rw [coverRecoveryIso_test_originalMap C D i f b ha _ _ rfl hz hf,
    coverRecoveryIso_test_originalMap C D j g c hg _ _ rfl hz' hf']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact chartTestRecoveryIso_originalMaps_transport_of_base
    C D i j f g b c hb hc z hf hf' ha hg

/-- Scheme-map affine tests retain independent source maps and a named common base path. -/
lemma coverRecoveryIso_affine_test_transport (i j : ι) {A : CommRingCat.{u}}
    (b : Spec A ⟶ Spec (C i).coverRing) (c : Spec A ⟶ Spec (C j).coverRing)
    (d d' : Spec A ⟶ Y) (z : Spec A ⟶ X)
    (hb : b ≫ (C i).cover = d) (hc : c ≫ (C j).cover = d')
    (hz : d ≫ p = z) (hz' : d' ≫ p = z) :
    (comparison d p z hz).inv.app (openGlued C D) ≫
        normalize b (C i).cover (C i).cover d d hb hb (coverRecoveryIso C D i).hom ≫
        (D.transport d d' (hz.trans hz'.symm)).hom =
      (comparison d' p z hz').inv.app (openGlued C D) ≫
        normalize c (C j).cover (C j).cover d' d' hc hc (coverRecoveryIso C D j).hom := by
  obtain ⟨b, rfl⟩ : ∃ β : (C i).coverRing ⟶ A, Spec.map β = b :=
    ⟨Spec.preimage b, Spec.map_preimage b⟩
  obtain ⟨c, rfl⟩ : ∃ γ : (C j).coverRing ⟶ A, Spec.map γ = c :=
    ⟨Spec.preimage c, Spec.map_preimage c⟩
  subst d d'
  exact coverRecoveryIso_affine_transport_of_base C D i j
    ((C i).ringMap ≫ b) ((C j).ringMap ≫ c) b c rfl rfl z
    (((C i).cover_spec_over _ b rfl).symm.trans hz)
    (((C j).cover_spec_over _ c rfl).symm.trans hz')
    ((C i).spec_square_of_ring_square _ b rfl)
    ((C j).spec_square_of_ring_square _ c rfl) hz hz'

end FLT.Mazur.SchemeAffineDescent
