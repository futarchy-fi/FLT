/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonBaseChartRecovery
public import FLT.Mazur.SchemeAffineCommonSectionTransportPullback

/-!
# Common-section reconstruction preserves original transport

The two recovered chart maps intertwine the original descent transport
between their independent source maps. This is the common-section input
to compatibility with the original descent overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private lemma section_reconstruction_transport {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {x y z : A} {v v' : B} (a : x ⟶ y) (b : x ⟶ z)
    (e : y ≅ z) (r : F.obj y ≅ v) (s : F.obj z ≅ v') (t : v ≅ v')
    (h : a ≫ e.hom = b) (he : r.symm ≪≫ F.mapIso e ≪≫ s = t) :
    F.map a ≫ r.hom ≫ t.hom = F.map b ≫ s.hom := by
  rw [← he]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]
  rw [← F.map_comp_assoc, h]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso
  Chart.refinementReconstruction

/-- Common-section reconstruction intertwines the original source transport. -/
lemma chartTestRecoveryIso_commonSection_transport (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base) :
    let ρ := (C i).commonBaseCrossRefinement (C j) f g w
    let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
    (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map
            (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
          ((C i).refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (comparison s ρ.leftChart.cover (Spec.map b ≫ (C i).cover)
          ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)).hom.app M ≫
        (D.transport (Spec.map b ≫ (C i).cover) (Spec.map c ≫ (C j).cover)
          (((C i).cover_spec_over f b hb).trans
            (w.trans ((C j).cover_spec_over g c hc).symm))).hom =
      (pullback s).map
          ((pullback (Spec.map ρ.ringMap)).map
              (chartTestRecoveryIso C D j
                (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom ≫
            ((C j).refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (comparison s ρ.rightChart.cover (Spec.map c ≫ (C j).cover)
          ((C i).commonCoverSection_rightChart (C j) f g b c hb hc w)).hom.app M := by
  let ρ := (C i).commonBaseCrossRefinement (C j) f g w
  let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
  refine section_reconstruction_transport (pullback s) _ _
    (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over)
    ((comparison s ρ.leftChart.cover (Spec.map b ≫ (C i).cover)
      ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)).app M)
    ((comparison s ρ.rightChart.cover (Spec.map c ≫ (C j).cover)
      ((C i).commonCoverSection_rightChart (C j) f g b c hb hc w)).app M)
    _ ?_ ?_
  · simpa only [Category.assoc] using
      chartTestRecoveryIso_commonBase_reconstruction C D i j f g w
  · exact (C i).commonCoverSection_transport (C j) f g b c hb hc w D

end FLT.Mazur.SchemeAffineDescent
