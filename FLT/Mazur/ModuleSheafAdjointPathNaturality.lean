/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionSections
public import FLT.Mazur.SchemeModulePullbackUnitSections
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Adjoint naturality of recovered chart restrictions

A compatibility equation for pullback chart recovery gives the corresponding
pushforward projection equation, including the actual composition comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafAdjointPathNaturality

open SheafPullbackPathComparison

/-- The adjoint of recovery by an open counit is its original ambient projection. -/
lemma projection_of_openCounit {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (G : X.Modules) (M : Y.Modules) (q : G ⟶ (pushforward i).obj M)
    (e : (pullback i).obj G ⟶ M)
    (he : e = (pullback i).map q ≫
      (ModuleSheafOverlapImageTransition.openCounitIso i M).hom) :
    (pullbackPushforwardAdjunction i).unit.app G ≫ (pushforward i).map e = q := by
  rw [he, ModuleSheafOpenImmersionSections.openCounitIso_hom]
  simpa only [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply] using
    ((pullbackPushforwardAdjunction i).homEquiv G M).apply_symm_apply q

/-- Pullback path compatibility gives compatibility of the actual adjoint projections. -/
lemma adjoint_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (h : a ≫ i = j) (G : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (u : (pullback i).obj G ⟶ M) (v : (pullback j).obj G ⟶ N)
    (e : (pullback a).obj M ⟶ N)
    (he : (pullback a).map u ≫ e = (comparison a i j h).hom.app G ≫ v) :
    (pullbackPushforwardAdjunction i).unit.app G ≫ (pushforward i).map u ≫
      (pushforward i).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
      (pushforward i).map ((pushforward a).map e) ≫
      (pushforwardComp a i).hom.app N ≫ (pushforwardCongr h).hom.app N =
        (pullbackPushforwardAdjunction j).unit.app G ≫ (pushforward j).map v := by
  subst j
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  simp only [Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
    ConcreteCategory.comp_apply]
  rw [N.presheaf.map_id]
  change e.app ((a ≫ i) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction a).unit.app M).app (i ⁻¹ᵁ U)
        (u.app (i ⁻¹ᵁ U) (((pullbackPushforwardAdjunction i).unit.app G).app U s))) =
    v.app ((a ≫ i) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction (a ≫ i)).unit.app G).app U s)
  have hn := congrArg (fun q ↦ q.app (i ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction i).unit.app G).app U s))
      ((pullbackPushforwardAdjunction a).unit.naturality u)
  change (((pullbackPushforwardAdjunction a).unit.app M).app (i ⁻¹ᵁ U)
      (u.app (i ⁻¹ᵁ U) (((pullbackPushforwardAdjunction i).unit.app G).app U s))) =
    ((pullback a).map u).app ((a ≫ i) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction a).unit.app ((pullback i).obj G)).app (i ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction i).unit.app G).app U s)) at hn
  rw [hn]
  have hh := congrArg (fun q ↦ q.app ((a ≫ i) ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction a).unit.app ((pullback i).obj G)).app (i ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction i).unit.app G).app U s))) he
  change e.app ((a ≫ i) ⁻¹ᵁ U)
      (((pullback a).map u).app ((a ≫ i) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction a).unit.app ((pullback i).obj G)).app (i ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction i).unit.app G).app U s))) =
    v.app ((a ≫ i) ⁻¹ᵁ U)
      (((pullbackComp a i).hom.app G).app ((a ≫ i) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction a).unit.app ((pullback i).obj G)).app (i ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction i).unit.app G).app U s))) at hh
  rw [SchemeModulePullbackUnitSections.comp_unit] at hh
  exact hh

/-- Specified ambient projections retain the adjoint path compatibility equation. -/
lemma projection_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (h : a ≫ i = j) (G : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (u : (pullback i).obj G ⟶ M) (v : (pullback j).obj G ⟶ N)
    (e : (pullback a).obj M ⟶ N)
    (q : G ⟶ (pushforward i).obj M) (r : G ⟶ (pushforward j).obj N)
    (hq : (pullbackPushforwardAdjunction i).unit.app G ≫ (pushforward i).map u = q)
    (hr : (pullbackPushforwardAdjunction j).unit.app G ≫ (pushforward j).map v = r)
    (he : (pullback a).map u ≫ e = (comparison a i j h).hom.app G ≫ v) :
    q ≫ (pushforward i).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
      (pushforward i).map ((pushforward a).map e) ≫
      (pushforwardComp a i).hom.app N ≫ (pushforwardCongr h).hom.app N = r := by
  rw [← hq, ← hr]
  simpa only [Category.assoc] using adjoint_comp a i j h G M N u v e he

end FLT.Mazur.ModuleSheafAdjointPathNaturality
