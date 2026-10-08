/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeModulePullbackUnits
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Pullback units on arbitrary opens

The pullback composition comparison preserves units before passing to global
sections. Restricting these units gives section maps on arbitrary source opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SchemeModulePullbackUnits

variable {X Y Z : Scheme.{u}}

/-- The composition comparison preserves the unit over every target open. -/
lemma comp_unit_open (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) :
    ((pullbackPushforwardAdjunction g).unit.app M).app U ≫
        ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U) ≫
          ((pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  ext m
  have h' := congrArg (fun k ↦ k.app U m) h
  change (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction g).unit.app M).app U m)) =
    ((pullbackComp f g).inv.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m) at h'
  change ((pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U)) _ = _
  erw [h']
  exact congrArg (fun k : (pullback (f ≫ g)).obj M ⟶ (pullback (f ≫ g)).obj M ↦
    k.app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m))
    ((pullbackComp f g).app M).inv_hom_id

/-- The unit restricted to a specified source open. -/
def openUnit (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : Γ(M, U) ⟶ Γ((pullback f).obj M, V) :=
  ((pullbackPushforwardAdjunction f).unit.app M).app U ≫
    ((pullback f).obj M).presheaf.map (homOfLE h).op

/-- Unit sections respect restriction of their target open. -/
lemma openUnit_restrict (f : X ⟶ Y) (M : Y.Modules) {U U' : Y.Opens}
    (j : U' ⟶ U) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U') :
    M.presheaf.map j.op ≫ openUnit f M U' V h =
      openUnit f M U V (h.trans (fun _ hx ↦ (leOfHom j) hx)) := by
  unfold openUnit
  have hn := ((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality j.op
  simp only [mapPresheaf_app] at hn
  change M.presheaf.map _ ≫ _ = _ ≫ ((pullback f).obj M).presheaf.map _ at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  rfl

/-- Unit sections respect morphisms of modules. -/
lemma openUnit_naturality (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    a.app U ≫ openUnit f N U V h =
      openUnit f M U V h ≫ ((pullback f).map a).app V := by
  unfold openUnit
  have hn := congrArg (fun k ↦ k.app U)
    ((pullbackPushforwardAdjunction f).unit.naturality a)
  simp only [Hom.comp_app, Functor.id_map, Functor.comp_map, pushforward_map_app] at hn
  have hr := ((pullback f).map a).mapPresheaf.naturality (homOfLE h).op
  simp only [mapPresheaf_app] at hr
  change _ ≫ ((pullback f).map a).app V =
    ((pullback f).map a).app (f ⁻¹ᵁ U) ≫ _ at hr
  rw [← Category.assoc, hn, Category.assoc, ← hr, Category.assoc]

/-- Composite pullback units agree on any chosen source and intermediate opens. -/
lemma openUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) :
    openUnit g M U V hV ≫ openUnit f ((pullback g).obj M) V W hW ≫
        ((pullbackComp f g).hom.app M).app W =
      openUnit (f ≫ g) M U W (hW.trans (fun _ hx ↦ hV hx)) := by
  unfold openUnit
  have hn := ((pullbackPushforwardAdjunction f).unit.app
    ((pullback g).obj M)).mapPresheaf.naturality (homOfLE hV).op
  simp only [mapPresheaf_app] at hn
  change ((pullback g).obj M).presheaf.map _ ≫ _ =
    _ ≫ ((pullback f).obj ((pullback g).obj M)).presheaf.map _ at hn
  simp only [← Category.assoc]
  rw [Category.assoc _ (((pullback g).obj M).presheaf.map _) _, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hc := ((pullbackComp f g).hom.app M).mapPresheaf.naturality
    (homOfLE (show W ≤ (f ≫ g) ⁻¹ᵁ U from hW.trans (fun _ hx ↦ hV hx))).op
  simp only [mapPresheaf_app] at hc
  change _ ≫ ((pullbackComp f g).hom.app M).app W = _ ≫ _ at hc
  have he : ((TopologicalSpace.Opens.map f.base).op.map (homOfLE hV).op ≫
      (homOfLE hW).op) = (homOfLE
        (show W ≤ (f ≫ g) ⁻¹ᵁ U from hW.trans (fun _ hx ↦ hV hx))).op :=
    Subsingleton.elim _ _
  rw [he]
  erw [hc]
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (((pullbackPushforwardAdjunction g).unit.app M).app U)]
  exact congrArg (· ≫ ((pullback (f ≫ g)).obj M).presheaf.map
    (homOfLE (show W ≤ (f ≫ g) ⁻¹ᵁ U from hW.trans (fun _ hx ↦ hV hx))).op)
    (comp_unit_open f g M U)

/-- Equality of geometric maps identifies their restricted unit sections. -/
lemma openUnit_congr {f g : X ⟶ Y} (e : f = g) (M : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    openUnit f M U V hf ≫ ((pullbackCongr e).hom.app M).app V =
      openUnit g M U V hg := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Hom.id_app, Category.comp_id]

/-- The normalized geometric comparison preserves restricted unit sections. -/
lemma openUnit_comparison (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (e : f ≫ g = k)
    (M : Z.Modules) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) (hk : W ≤ k ⁻¹ᵁ U) :
    openUnit g M U V hV ≫ openUnit f ((pullback g).obj M) V W hW ≫
        ((SheafPullbackPathComparison.comparison f g k e).hom.app M).app W =
      openUnit k M U W hk := by
  change _ ≫ _ ≫ (((pullbackComp f g).hom.app M).app W ≫
    ((pullbackCongr e).hom.app M).app W) = _
  rw [← Category.assoc, ← Category.assoc, Category.assoc (openUnit g M U V hV),
    openUnit_comp, openUnit_congr]

end FLT.Mazur.SchemeModulePullbackUnits
