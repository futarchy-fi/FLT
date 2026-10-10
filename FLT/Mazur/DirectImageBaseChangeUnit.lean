/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeMate

/-!
# Unit normalization of the actual direct-image comparison

Transposing the base-change mate along the base morphism gives the original
pullback unit on the total space, followed by the pushforward square.
This identity applies to every module sheaf and every commutative square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.DirectImageBaseChange
open SchemePullbackSquare
universe u
private lemma conj_inv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) :
    conjugateEquiv a₂ a₁ e.inv = inv (conjugateEquiv a₁ a₂ e.hom) := by
  apply (cancel_epi (conjugateEquiv a₁ a₂ e.hom)).mp
  rw [conjugateEquiv_comp, e.inv_hom_id, conjugateEquiv_id, IsIso.hom_inv_id]
private lemma conj_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  rw [← Iso.symm_inv (pullbackComp f g), conj_inv]
  simp only [Iso.symm_hom, conjugateEquiv_pullbackComp_inv]
  exact IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)
private lemma conj_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, conjugateEquiv_id]
  ext M U x
  simp
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f)
/-- The pullback square is conjugate to the original pushforward square. -/
lemma conjugate_square :
    conjugateEquiv
      ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction p))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction q))
      (squareIso f q g p w).hom =
      (pushforwardComp p f).hom ≫ (pushforwardCongr w).inv ≫
        (pushforwardComp q g).inv := by
  change conjugateEquiv _ _
    ((pullbackComp q g).hom ≫ (pullbackCongr w).hom ≫ (pullbackComp p f).inv) = _
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (p ≫ f)) _]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (q ≫ g)) _]
  rw [conjugateEquiv_pullbackComp_inv, conj_congr, conj_comp_hom]

/-- The actual base-change mate has the original total-space unit as its transpose. -/
lemma comparison_unit_map (M : X.Modules) :
    (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map (comparison p q f g w M) =
    (pushforward f).map ((pullbackPushforwardAdjunction p).unit.app M) ≫
      ((pushforwardComp p f).hom ≫ (pushforwardCongr w).inv ≫
        (pushforwardComp q g).inv).app ((pullback p).obj M) := by
  let δ := (pushforwardComp p f).hom ≫ (pushforwardCongr w).inv ≫
    (pushforwardComp q g).inv
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction p))
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction q))
    (squareIso f q g p w).hom ((pushforward f).obj M)
  rw [conjugate_square, Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change _ ≫ δ.app _ = _ at h
  have hh := congrArg (fun k ↦ k ≫ (pushforward q ⋙ pushforward g).map
    ((pullback p).map ((pullbackPushforwardAdjunction f).counit.app M))) h
  simp only [Category.assoc] at hh
  rw [← δ.naturality] at hh
  simp only [Functor.comp_map] at hh
  have hn := (pullbackPushforwardAdjunction p).unit.naturality
    ((pullbackPushforwardAdjunction f).counit.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← (pushforward f).map_comp_assoc] at hh
  erw [← hn] at hh
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [← Category.assoc, (pullbackPushforwardAdjunction f).right_triangle_components] at hh
  erw [Category.id_comp] at hh
  simpa only [comparison, δ, Adjunction.homEquiv_unit, Functor.map_comp,
    Functor.comp_obj, Functor.id_obj, Category.assoc] using hh.symm
end FLT.Mazur.DirectImageBaseChange
