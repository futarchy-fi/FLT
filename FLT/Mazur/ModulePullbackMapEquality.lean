/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSealedPullbackRatio

/-!
# Section transport along equality of scheme maps

Use a sealed module isomorphism to change the map defining a pullback. The
section identity is proved for arbitrary schemes, so a concrete component
comparison can be sealed without converting through its scheme construction.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} {f g : X ⟶ Y}

/-- Equal maps give a sealed isomorphism between their module pullbacks. -/
irreducible_def pullbackMapEqIso (hfg : f = g) (M : Y.Modules) :
    (pullback f).obj M ≅ (pullback g).obj M :=
  eqToIso (congrArg (fun k ↦ (pullback k).obj M) hfg)

/-- The equality comparison preserves every actual pulled-back section. -/
lemma pullbackMapEqIso_section (hfg : f = g) (M : Y.Modules) (s : Γ(M, ⊤)) :
    (pullbackMapEqIso hfg M).hom.app ⊤ (pullGlobal f M s) = pullGlobal g M s := by
  subst g
  rw [pullbackMapEqIso_def]
  simp only [eqToIso_refl, Iso.refl_hom, Hom.id_app, AddCommGrpCat.id_apply]

/-- A map equality transports a component comparison at the level of sections. -/
lemma pullbackMapEqIso_comp_section (hfg : f = g) (M : Y.Modules) {N : X.Modules}
    (e : (pullback g).obj M ≅ N) (s : Γ(M, ⊤)) :
    ((pullbackMapEqIso hfg M ≪≫ e).hom.app ⊤) (pullGlobal f M s) =
      e.hom.app ⊤ (pullGlobal g M s) := by
  simp only [Iso.trans_hom, Hom.comp_app, AddCommGrpCat.comp_apply,
    pullbackMapEqIso_section]

/-- An identified sealed comparison has the same action on sections. -/
lemma pullbackMapEqIso_comp_section_of_eq (hfg : f = g) (M : Y.Modules) {N : X.Modules}
    (e : (pullback g).obj M ≅ N) (e' : (pullback f).obj M ≅ N)
    (he : e' = pullbackMapEqIso hfg M ≪≫ e) (s : Γ(M, ⊤)) :
    e'.hom.app ⊤ (pullGlobal f M s) = e.hom.app ⊤ (pullGlobal g M s) := by
  subst e'
  exact pullbackMapEqIso_comp_section hfg M e s

/-- Named section values can be transported without conversion through their definitions. -/
lemma pullbackMapEqIso_comp_section_value (hfg : f = g) (M : Y.Modules) {N : X.Modules}
    (e : (pullback g).obj M ≅ N) (e' : (pullback f).obj M ≅ N)
    (he : e' = pullbackMapEqIso hfg M ≪≫ e) (s : Γ(M, ⊤)) (t : Γ(N, ⊤))
    (ht : e.hom.app ⊤ (pullGlobal g M s) = t) :
    e'.hom.app ⊤ (pullGlobal f M s) = t :=
  (pullbackMapEqIso_comp_section_of_eq hfg M e e' he s).trans ht

end FLT.Mazur.FCurve
