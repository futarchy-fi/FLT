/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonSectionRecovery
public import FLT.Mazur.SchemeAffineExplicitCommonSectionMaps

/-!
# Sealed common-section equality

The proved equality along the constructed section is exposed through
sealed maps to keep specialization independent of pullback implementation details.
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

/-- The actual common section equates the sealed left and right reconstruction maps. -/
lemma chartTestRecoveryIso_commonSection_maps (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
    (C i).commonSectionLeftMap D (C j) f g w s (Spec.map b ≫ (C i).cover)
        ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)
        (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom =
      (C i).commonSectionRightMap D (C j) f g w s (Spec.map b ≫ (C i).cover)
        (((C i).commonCoverSection_rightChart (C j) f g b c hb hc w).trans hs.symm)
        (chartTestRecoveryIso C D j
          (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom := by
  apply Chart.commonSectionMaps_eq_of_raw
  exact chartTestRecoveryIso_commonSection C D i j f g b c hb hc w hs

end FLT.Mazur.SchemeAffineDescent
