/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionMap
public import FLT.Mazur.LinePullbackRestriction
/-!
# Endpoint transport through a line comparison

A component line comparison and a commuting incidence triangle identify the
endpoint pullback with the actual node line. Canonical sections, normalized
values, and scalar cancellation pass through this identification.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineEndpointTransport
open FCurve
variable {X Y Z : Scheme.{u}}

/-- Identify the endpoint of a compared line with the common target fiber. -/
def iso (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback f).obj L ≅ M) :
    (pullback g).obj M ≅ (pullback q).obj L :=
  (pullback g).mapIso e.symm ≪≫ (pullbackComp g f).app L ≪≫ (pullbackCongr w).app L

/-- A section-preserving comparison preserves its endpoint value. -/
lemma canonical (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback f).obj L ≅ M)
    (c : Γ(L, ⊤)) (d : Γ(M, ⊤)) (he : e.hom.app ⊤ (pullGlobal f L c) = d) :
    (iso f g q w e).hom.app ⊤ (pullGlobal g M d) = pullGlobal q L c := by
  subst q
  change ((pullbackCongr rfl).hom.app L).app ⊤
    (((pullbackComp g f).hom.app L).app ⊤
      (((pullback g).map e.inv).app ⊤ (pullGlobal g M d))) = _
  rw [pullGlobal_naturality, sectionIso_inv_of_eq e ⊤ _ _ he, pullGlobal_comp_hom]
  rfl

/-- A normalized endpoint formula transports to the common target line. -/
lemma value (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback f).obj L ≅ M)
    (c : Γ(L, ⊤)) (d : Γ(M, ⊤)) (he : e.hom.app ⊤ (pullGlobal f L c) = d)
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : pullGlobal g M s = r • pullGlobal g M d) :
    (iso f g q w e).hom.app ⊤ (pullGlobal g M s) = r • pullGlobal q L c := by
  rw [hs, Hom.app_smul, canonical f g q w e c d he]

/-- Scalar cancellation transports through the actual endpoint isomorphism. -/
lemma canonical_cancel (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback f).obj L ≅ M)
    (c : Γ(L, ⊤)) (d : Γ(M, ⊤)) (he : e.hom.app ⊤ (pullGlobal f L c) = d)
    (hd : Function.Injective (fun r : Γ(X, ⊤) ↦ r • pullGlobal g M d)) :
    Function.Injective (fun r : Γ(X, ⊤) ↦ r • pullGlobal q L c) := by
  intro r t h
  apply hd
  apply (ConcreteCategory.bijective_of_isIso ((iso f g q w e).hom.app ⊤)).1
  simpa only [Hom.app_smul, canonical f g q w e c d he] using h
/-- Geometric line restriction is evaluation through the endpoint comparison. -/
lemma along_eq_transport (f : Y ⟶ Z) (g : X ⟶ Y) (q : X ⟶ Z) (w : g ≫ f = q)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback f).obj L ≅ M)
    (s : Γ((pullback f).obj L, ⊤)) :
    (LinePullbackRestriction.along g f q w L).app ⊤ s =
      (iso f g q w e).hom.app ⊤ (pullGlobal g M (e.hom.app ⊤ s)) := by
  subst q
  change (LinePullbackRestriction.restriction g f L).app ⊤ s =
    ((pullbackCongr rfl).hom.app L).app ⊤
      (((pullbackComp g f).hom.app L).app ⊤
        (((pullback g).map e.inv).app ⊤ (pullGlobal g M (e.hom.app ⊤ s))))
  rw [pullGlobal_naturality, sectionIso_inv_hom, LinePullbackRestriction.restriction_appTop]
  rfl
end FLT.Mazur.LineEndpointTransport
