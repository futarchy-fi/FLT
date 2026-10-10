/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesPrincipalModel
public import FLT.Mazur.BaseAdicReesCocycle
public import FLT.Mazur.BaseAdicReesOverlap

/-!
# Actual sheaf restrictions of relative Rees models

Every affine inclusion gives a normalized morphism of the relative model
sheaves. On principal inclusions it is the previously constructed isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) {U V W : X.affineOpens}

/-- The geometric map induced by the original relative ring restriction. -/
def modelMap (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f V
    Spec (.of (Γ(X, U.1) ⊗[R] reesAlgebra J)) ⟶
      Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J)) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  exact Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)

/-- Relative model inclusions are open immersions. -/
instance modelMap_isOpenImmersion (h : U.1 ≤ V.1) :
    IsOpenImmersion (modelMap f J h) := relativeRingRestriction_isOpenImmersion f J h

/-- Model chart inclusions compose along the original affine inclusions. -/
lemma modelMap_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    modelMap f J h ≫ modelMap f J k = modelMap f J (h.trans k) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  let _ := chartAlgebra f W
  unfold modelMap
  rw [← Spec.map_comp]
  exact congrArg (fun a ↦ Spec.map (CommRingCat.ofHom a.toRingHom))
    (relativeRingRestriction_comp f J h k)

variable [IsLocallyNoetherian X] [IsNoetherianRing R]
  (M : X.Modules) [M.IsFinitePresentation]

/-- Original coefficients induce a morphism of actual pullback model sheaves. -/
def modelRestriction (h : U.1 ≤ V.1) :
    (pullback (modelMap f J h)).obj (modelSheaf f J V M) ⟶ modelSheaf f J U M := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  exact AffineTildeSemilinearMap.map
    (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
    (nativeModule f J M V) (nativeModule f J M U) (nativeRestriction f J M h)

omit [IsNoetherianRing R] in
/-- The general morphism agrees with the normalized principal isomorphism. -/
lemma modelRestriction_principal (V : X.affineOpens) (r : Γ(X, V.1)) :
    modelRestriction f J M (U := ⟨X.basicOpen r, V.2.basicOpen r⟩)
      (V := V) (X.basicOpen_le r) = (principalModelIso f J M V r).hom :=
  (principalModelIso_hom f J M V r).symm

/-- The actual coefficient sheaf morphism is invertible on a principal inclusion. -/
instance modelRestriction_principal_isIso (V : X.affineOpens) (r : Γ(X, V.1)) :
    IsIso (modelRestriction f J M (U := ⟨X.basicOpen r, V.2.basicOpen r⟩)
      (V := V) (X.basicOpen_le r)) := by
  rw [modelRestriction_principal]
  infer_instance

omit [IsNoetherianRing R] in
/-- Invertibility is independent of how the smaller principal chart is presented. -/
lemma modelRestriction_isIso_of_basicOpen (h : U.1 ≤ V.1)
    (r : Γ(X, V.1)) (hr : U.1 = X.basicOpen r) :
    IsIso (modelRestriction f J M h) := by
  have he : U = ⟨X.basicOpen r, V.2.basicOpen r⟩ := Subtype.ext hr
  subst U
  exact modelRestriction_principal_isIso f J M V r

end FLT.Mazur.BaseAdicRees
