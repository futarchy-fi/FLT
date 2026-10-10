/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionMaps
public import FLT.Mazur.SchemeAffineCommonSectionCancellation

/-!
# Cancellation of the constructed common section

Apply cross-refinement cancellation to the constructed common cover and
its section. Original chart reconstruction therefore agrees on source tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso
  Chart.refinementReconstruction Chart.reconstruction

/-- Cancel the constructed common section in the original chart coordinates. -/
lemma chartTestRecoveryIso_commonSection_originalMaps (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    (C i).sectionOriginalMap D f (Spec.map b) (by rw [← Spec.map_comp, hb])
        (Spec.map b ≫ (C i).cover) rfl
        (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom =
      (C j).sectionOriginalMap D g (Spec.map c) (by rw [← Spec.map_comp, hc])
        (Spec.map b ≫ (C i).cover) hs.symm
        (chartTestRecoveryIso C D j
          (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom := by
  let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
  exact (C i).commonSectionOriginalMap_eq D (C j) f g w s
    ((C i).commonCoverSection_spec_base f b hb (C j) g c hc)
    (Spec.map b) ((C i).commonCoverSection_spec_left f b hb (C j) g c hc)
    (by rw [← Spec.map_comp, hb])
    (Spec.map c) ((C i).commonCoverSection_spec_right f b hb (C j) g c hc)
    (by rw [← Spec.map_comp, hc]) (Spec.map b ≫ (C i).cover)
    ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)
    (((C i).commonCoverSection_rightChart (C j) f g b c hb hc w).trans hs.symm)
    rfl hs.symm
    (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom
    (chartTestRecoveryIso C D j (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom
    (chartTestRecoveryIso_commonSection_maps C D i j f g b c hb hc w hs)

/-- Original chart reconstructions agree for affine lifts of the same source map. -/
lemma chartTestRecoveryIso_commonSection_comparison (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
        (comparison (Spec.map b) (Spec.map (C i).ringMap) (Spec.map f)
          (by rw [← Spec.map_comp, hb])).inv.app ((C i).sheaf D) ≫
        (pullback (Spec.map b)).map ((C i).reconstruction D).hom ≫
        (comparison (Spec.map b) (C i).cover (Spec.map b ≫ (C i).cover) rfl).hom.app M =
      (chartTestRecoveryIso C D j (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom ≫
        (comparison (Spec.map c) (Spec.map (C j).ringMap) (Spec.map g)
          (by rw [← Spec.map_comp, hc])).inv.app ((C j).sheaf D) ≫
        (pullback (Spec.map c)).map ((C j).reconstruction D).hom ≫
        (comparison (Spec.map c) (C j).cover (Spec.map b ≫ (C i).cover) hs.symm).hom.app M := by
  have h := chartTestRecoveryIso_commonSection_originalMaps C D i j f g b c hb hc w hs
  unfold Chart.sectionOriginalMap at h
  exact h

end FLT.Mazur.SchemeAffineDescent
