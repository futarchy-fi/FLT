/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonBaseChartRecovery
public import FLT.Mazur.SchemeAffineCommonSectionTransport

/-!
# Equality of original reconstructions along the common-cover section

The constructed common-cover section makes the two actual chart
reconstructions agree when the prescribed original source maps agree.
The equality follows from the descent transport and its diagonal law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private lemma section_reconstruction {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {x y z : A} {v : B} (a : x ⟶ y) (b : x ⟶ z)
    (e : y ≅ z) (r : F.obj y ≅ v) (s : F.obj z ≅ v)
    (h : a ≫ e.hom = b) (he : r.symm ≪≫ F.mapIso e ≪≫ s = Iso.refl v) :
    F.map a ≫ r.hom = F.map b ≫ s.hom := by
  have ht := congrArg (fun i ↦ r.hom ≫ i.hom) he
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id] at ht
  rw [← ht, ← F.map_comp_assoc, h]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued chartTestRecoveryIso
  Chart.refinementReconstruction

/-- The actual reconstructed chart maps coincide along a section with equal source maps. -/
lemma chartTestRecoveryIso_commonSection (i j : ι) {A : CommRingCat.{u}}
    (f : (C i).baseRing ⟶ A) (g : (C j).baseRing ⟶ A)
    (b : (C i).coverRing ⟶ A) (c : (C j).coverRing ⟶ A)
    (hb : (C i).ringMap ≫ b = f) (hc : (C j).ringMap ≫ c = g)
    (w : Spec.map f ≫ (C i).base = Spec.map g ≫ (C j).base)
    (hs : Spec.map b ≫ (C i).cover = Spec.map c ≫ (C j).cover) :
    let ρ := (C i).commonBaseCrossRefinement (C j) f g w
    let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
    (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map
            (chartTestRecoveryIso C D i (Spec.map f ≫ (C i).base) (Spec.map f) rfl).hom ≫
          ((C i).refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (comparison s ρ.leftChart.cover (Spec.map b ≫ (C i).cover)
          ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)).hom.app M =
      (pullback s).map
          ((pullback (Spec.map ρ.ringMap)).map
              (chartTestRecoveryIso C D j
                (Spec.map f ≫ (C i).base) (Spec.map g) w.symm).hom ≫
            ((C j).refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (comparison s ρ.rightChart.cover (Spec.map b ≫ (C i).cover)
          (((C i).commonCoverSection_rightChart (C j) f g b c hb hc w).trans
            hs.symm)).hom.app M := by
  let ρ := (C i).commonBaseCrossRefinement (C j) f g w
  let s := Spec.map ((C i).commonCoverSection f b hb (C j) g c hc)
  refine section_reconstruction (pullback s) _ _
    (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over)
    ((comparison s ρ.leftChart.cover (Spec.map b ≫ (C i).cover)
      ((C i).commonCoverSection_leftChart (C j) f g b c hb hc w)).app M)
    ((comparison s ρ.rightChart.cover (Spec.map b ≫ (C i).cover)
      (((C i).commonCoverSection_rightChart (C j) f g b c hb hc w).trans hs.symm)).app M)
    ?_ ?_
  · simpa only [Category.assoc] using
      chartTestRecoveryIso_commonBase_reconstruction C D i j f g w
  · exact (C i).commonCoverSection_transport_self (C j) f g b c hb hc w D hs

end FLT.Mazur.SchemeAffineDescent
