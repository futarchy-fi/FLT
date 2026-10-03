/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleTensorPowerSection
/-!
# Section maps of module isomorphisms

Composition, inverse, tensor congruence, and pullback identities for actual
sections, with no expansion of the chosen geometric isomorphisms.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}
/-- Composing module isomorphisms composes their section maps. -/
lemma sectionIso_trans {M N P : X.Modules} (e : M ≅ N) (f : N ≅ P)
    (U : X.Opens) (s : Γ(M, U)) :
    (e ≪≫ f).hom.app U s = f.hom.app U (e.hom.app U s) := rfl
/-- An inverse section map cancels its forward map. -/
lemma sectionIso_inv_hom {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) : e.inv.app U (e.hom.app U s) = s :=
  congrArg (fun k ↦ k.app U s) e.hom_inv_id
/-- A forward section map cancels its inverse. -/
lemma sectionIso_hom_inv {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(N, U)) : e.hom.app U (e.inv.app U s) = s :=
  congrArg (fun k ↦ k.app U s) e.inv_hom_id
/-- Section preservation determines preservation by the inverse. -/
lemma sectionIso_inv_of_eq {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) (h : e.hom.app U s = t) :
    e.inv.app U t = s := by
  rw [← h, sectionIso_inv_hom]
/-- Tensor congruence carries pure sections to pure sections. -/
lemma sectionTensor_congr {M N M' N' : X.Modules} (e : M ≅ M') (f : N ≅ N')
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (ModuleSheafTensor.congr e f).hom.app U (ModuleSheafTensor.pure M N U s t) =
      ModuleSheafTensor.pure M' N' U (e.hom.app U s) (f.hom.app U t) :=
  ModuleSheafTensor.map_pure e.hom f.hom U s t
/-- A commuting section-morphism square preserves actual pulled-back sections. -/
lemma pullGlobal_section_map (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (s : structureModule Y ⟶ M) (t : structureModule X ⟶ N)
    (e : (pullback f).obj M ⟶ N)
    (h : (pullback f).map s ≫ e = (modulePullbackUnitIso f).hom ≫ t) :
    e.app ⊤ (pullGlobal f M (s.app ⊤ (1 : Γ(Y, ⊤)))) =
      t.app ⊤ (1 : Γ(X, ⊤)) := by
  rw [pullGlobal_hom]
  have hh := congrArg (fun k ↦ k.app ⊤
    ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)))) h
  change e.app ⊤ _ = t.app ⊤ ((modulePullbackUnitIso f).hom.app ⊤
    ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)))) at hh
  rw [sectionIso_hom_inv] at hh
  exact hh
/-- Section preservation composes through an intermediate section. -/
lemma sectionIso_trans_of_eq {M N P : X.Modules} (e : M ≅ N) (f : N ≅ P)
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) (v : Γ(P, U))
    (he : e.hom.app U s = t) (hf : f.hom.app U t = v) :
    (e ≪≫ f).hom.app U s = v := by
  rw [sectionIso_trans, he, hf]
end FLT.Mazur.FCurve
