/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionTransportRecovery
public import FLT.Mazur.SchemeAffineCommonSectionTransportEquation

/-!
# Sealed common-section transport

The original transport equation along the constructed section is expressed
through sealed maps with distinct original source targets.
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

/-- The actual common section intertwines original transport through sealed maps. -/
lemma chartTestRecoveryIso_commonSection_maps_transport (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base) :
    let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
    (C i).commonSectionLeftMap D (C j) f g w s (Spec.map b ≫ (C i).cover)
        ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)
        (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (((C i).cover_spec_over f b hb).trans
            (w.trans ((C j).cover_spec_over g c hc).symm))).hom =
      (C i).commonSectionRightMap D (C j) f g w s (Spec.map c ≫ (C j).cover)
        ((C i).commonCoverSection_rightChart (C j) f g b c hb hc w)
        (chartTestRecoveryIso C D j
          (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom := by
  apply Chart.commonSectionMaps_postcomp_of_raw
  exact chartTestRecoveryIso_commonSection_transport C D i j f g b c hb hc w

end FLT.Mazur.SchemeAffineDescent
