/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionTransportMaps
public import FLT.Mazur.SchemeAffineCommonSectionPostcomposition

/-!
# Original chart reconstruction intertwines descent transport

Cancel the constructed section in the genuine transport equation. The two
original source maps need only agree after composition with the base map.
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
  Chart.refinementReconstruction

/-- Original reconstruction intertwines transport between distinct source maps. -/
lemma chartTestRecoveryIso_originalMaps_transport_of_square (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (ha : Spec.map b ≫ Spec.map (C i).ringMap = Spec.map f)
    (hg : Spec.map c ≫ Spec.map (C j).ringMap = Spec.map g) :
    (C i).sectionOriginalMap D f (Spec.map b) ha
        (Spec.map b ≫ (C i).cover) rfl
        (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (((C i).cover_spec_over f b hb).trans
            (w.trans ((C j).cover_spec_over g c hc).symm))).hom =
      (C j).sectionOriginalMap D g (Spec.map c) hg
        (Spec.map c ≫ (C j).cover) rfl
        (chartTestRecoveryIso C D j
          (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom := by
  exact (C i).commonSectionOriginalMap_postcomp D (C j) f g w
    (Spec.map ((C i).commonCoverSection f b hb (C j) g c hc))
    ((C i).commonCoverSection_spec_base f b hb (C j) g c hc)
    (Spec.map b) ((C i).commonCoverSection_spec_left f b hb (C j) g c hc)
    ha
    (Spec.map c) ((C i).commonCoverSection_spec_right f b hb (C j) g c hc)
    hg (Spec.map b ≫ (C i).cover)
    ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)
    (Spec.map c ≫ (C j).cover)
    ((C i).commonCoverSection_rightChart (C j) f g b c hb hc w)
    rfl rfl _
    (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom
    (chartTestRecoveryIso C D j (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom
    (chartTestRecoveryIso_commonSection_maps_transport C D i j f g b c hb hc w)

end FLT.Mazur.SchemeAffineDescent
