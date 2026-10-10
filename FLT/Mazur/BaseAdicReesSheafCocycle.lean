/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSheafMap
public import FLT.Mazur.AffineTildeMorphismCoherence

/-!
# Sheaf cocycles for the actual relative Rees restrictions

The composition law for original coefficients gives the actual sheaf
composition law, including the canonical iterated-pullback comparison.
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
  (J : Ideal R) [IsLocallyNoetherian X] [IsNoetherianRing R]
  (M : X.Modules) [M.IsFinitePresentation] {U V W : X.affineOpens}

attribute [local irreducible] Scheme.Modules.pullback AffineTildeSemilinearMap.map
attribute [local irreducible] relativeRingRestriction relativeRestriction
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The geometric comparison between iterated and direct model pullbacks. -/
def modelCompositeIso (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    (pullback (modelMap f J h)).obj
        ((pullback (modelMap f J k)).obj (modelSheaf f J W M)) ≅
      (pullback (modelMap f J (h.trans k))).obj (modelSheaf f J W M) :=
  AffineIteratedPullbackSections.compositeIso (modelMap f J h) (modelMap f J k)
    (modelMap f J (h.trans k)) (modelMap_comp f J h k) (modelSheaf f J W M)

omit [IsNoetherianRing R] in
/-- The geometric comparison agrees with its affine coefficient presentation. -/
lemma modelCompositeIso_eq (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f V
    let _ := chartAlgebra f W
    modelCompositeIso f J M h k = AffineIteratedPullbackSections.compositeIso
      (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom))
      (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J k).toRingHom))
      (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J (h.trans k)).toRingHom))
      (modelMap_comp f J h k) (tilde (nativeModule f J M W)) := rfl

omit [IsLocallyNoetherian X] [IsNoetherianRing R] [M.IsFinitePresentation] in
/-- Bundled native restrictions compose on each original coefficient element. -/
lemma nativeRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1)
    (m : nativeModule f J M W) :
    nativeRestriction f J M h (nativeRestriction f J M k m) =
      nativeRestriction f J M (h.trans k) m := by
  exact relativeRestriction_comp f J M h k m

attribute [local irreducible] nativeRestriction

omit [IsNoetherianRing R] in
/-- Original coefficient sections normalize the actual restriction morphism. -/
lemma modelRestriction_unit (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f V
    ∀ m : nativeModule f J M V,
      moduleSpecΓFunctor.map (modelRestriction f J M h)
          (AffineTildePullbackSectionMap.unit
            (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
            (nativeModule f J M V) m) =
        (tilde.toTildeΓNatIso (R := .of (Γ(X, U.1) ⊗[R] reesAlgebra J))).hom.app
          (nativeModule f J M U) (nativeRestriction f J M h m) := by
  intro _ _ m
  exact AffineTildePullbackSectionMap.semilinearMap_unit
    (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
    (nativeModule f J M V) (nativeModule f J M U) (nativeRestriction f J M h) m

attribute [local irreducible] modelRestriction

omit [IsNoetherianRing R] in
/-- Actual model restrictions satisfy the triple-inclusion sheaf cocycle. -/
lemma modelRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    (modelCompositeIso f J M h k).inv ≫
        (pullback (modelMap f J h)).map (modelRestriction f J M k) ≫
        modelRestriction f J M h = modelRestriction f J M (h.trans k) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  let _ := chartAlgebra f W
  rw [modelCompositeIso_eq f J M h k]
  exact AffineTildeMorphismCoherence.hom_comp
    (CommRingCat.ofHom (relativeRingRestriction f J k).toRingHom)
    (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
    (CommRingCat.ofHom (relativeRingRestriction f J (h.trans k)).toRingHom)
    (modelMap_comp f J h k)
    (nativeModule f J M W) (nativeModule f J M V) (nativeModule f J M U)
    (modelRestriction f J M k) (modelRestriction f J M h)
    (modelRestriction f J M (h.trans k))
    (nativeRestriction f J M k) (nativeRestriction f J M h)
    (nativeRestriction f J M (h.trans k))
    (modelRestriction_unit f J M k) (modelRestriction_unit f J M h)
    (modelRestriction_unit f J M (h.trans k)) (nativeRestriction_comp f J M h k)

attribute [local irreducible] modelCompositeIso

omit [IsNoetherianRing R] in
/-- Forward composition retains the canonical geometric pullback comparison. -/
lemma modelRestriction_comp_forward (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    (pullback (modelMap f J h)).map (modelRestriction f J M k) ≫
        modelRestriction f J M h =
      (modelCompositeIso f J M h k).hom ≫ modelRestriction f J M (h.trans k) := by
  rw [← modelRestriction_comp f J M h k, Iso.hom_inv_id_assoc]

omit [IsNoetherianRing R] in
/-- A common principal refinement makes the pullback of any model restriction invertible. -/
lemma modelRestriction_pullback_isIso (h : U.1 ≤ V.1) (k : V.1 ≤ W.1)
    (r : Γ(X, V.1)) (s : Γ(X, W.1))
    (hr : U.1 = X.basicOpen r) (hs : U.1 = X.basicOpen s) :
    IsIso ((pullback (modelMap f J h)).map (modelRestriction f J M k)) := by
  let _ := modelRestriction_isIso_of_basicOpen f J M h r hr
  let _ := modelRestriction_isIso_of_basicOpen f J M (h.trans k) s hs
  have : IsIso ((pullback (modelMap f J h)).map (modelRestriction f J M k) ≫
      modelRestriction f J M h) := by
    rw [modelRestriction_comp_forward]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (modelRestriction f J M h)

end FLT.Mazur.BaseAdicRees
