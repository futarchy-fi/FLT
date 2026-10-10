/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSheafCocycle
public import FLT.Mazur.BaseAdicReesCommonRefinement
public import FLT.Mazur.ModuleSheafPullbackIsoDetection

/-!
# Pullback isomorphisms for all affine relative Rees inclusions

The sheaf cocycle and common principal covers extend the original principal
isomorphisms to every affine inclusion, using actual open-immersion pullbacks.
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
  (J : Ideal R) [IsLocallyNoetherian X]
  (M : X.Modules) [M.IsFinitePresentation] {U V : X.affineOpens}

attribute [local irreducible] modelRestriction modelCompositeIso Scheme.Modules.pullback

/-- Every original affine model restriction is an isomorphism. -/
lemma modelRestriction_isIso (h : U.1 ≤ V.1) : IsIso (modelRestriction f J M h) := by
  let _ := chartAlgebra f U
  let C := {rs : Γ(X, U.1) × Γ(X, V.1) // X.basicOpen rs.1 = X.basicOpen rs.2}
  let W (c : C) : X.affineOpens := ⟨X.basicOpen c.val.1, U.2.basicOpen c.val.1⟩
  let g (c : C) : (W c).1 ≤ U.1 := X.basicOpen_le c.val.1
  let Z (c : C) : Scheme := by
    let _ := chartAlgebra f (W c)
    exact Spec (.of (Γ(X, (W c).1) ⊗[R] reesAlgebra J))
  let k (c : C) : Z c ⟶ Spec (.of (Γ(X, U.1) ⊗[R] reesAlgebra J)) :=
    modelMap f J (g c)
  let _ (c : C) : IsOpenImmersion (k c) := modelMap_isOpenImmersion f J (g c)
  apply ModuleSheafPullbackIsoDetection.isIso_of_openImmersionPullbacks
    (modelRestriction f J M h) Z k
  · intro x
    obtain ⟨r, s, hrs, hx⟩ := modelMap_exists_common_principal f J h x
    exact ⟨⟨(r, s), hrs⟩, hx⟩
  · intro c
    exact modelRestriction_pullback_isIso f J M (g c) h c.val.1 c.val.2 rfl c.property

/-- The actual pullback comparison for an arbitrary affine inclusion. -/
def modelPullbackIso (h : U.1 ≤ V.1) :
    (pullback (modelMap f J h)).obj (modelSheaf f J V M) ≅ modelSheaf f J U M := by
  let _ := modelRestriction_isIso f J M h
  exact asIso (modelRestriction f J M h)

/-- The isomorphism retains the originally constructed coefficient restriction. -/
lemma modelPullbackIso_hom (h : U.1 ≤ V.1) :
    (modelPullbackIso f J M h).hom = modelRestriction f J M h := rfl

end FLT.Mazur.BaseAdicRees
