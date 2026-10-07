/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildeSemilinearMap
public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Bundled original sections of affine pullbacks

Bundling the original-section map avoids repeated unfolding of inverse images
of the top open when these formulas are applied to large concrete rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineTildePullbackSectionMap

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R)

/-- Original coefficients enter the actual sheaf pullback through the two adjunction units. -/
def unit : M →+ moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj (tilde M)) :=
  (AffineIteratedPullbackSections.specUnit φ (tilde M)).comp
    ((tilde.toTildeΓNatIso (R := R)).hom.app M).hom.toAddMonoidHom

/-- Bundled global sections of a scalar-extension map have the original unit-tensor formula. -/
lemma map_unit (N : ModuleCat S) (k : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) (m : M) :
    moduleSpecΓFunctor.map (AffineTildePullbackMap.map φ M N k) (unit φ M m) =
      (tilde.toTildeΓNatIso (R := S)).hom.app N
        (k ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m)) :=
  AffineTildePullbackMap.map_unit φ M N k m

/-- Semilinear maps retain the original coefficient on bundled global sections. -/
lemma semilinearMap_unit (N : ModuleCat S)
    (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) (m : M) :
    moduleSpecΓFunctor.map (AffineTildeSemilinearMap.map φ M N g) (unit φ M m) =
      (tilde.toTildeΓNatIso (R := S)).hom.app N (g m) :=
  AffineTildeSemilinearMap.map_unit φ M N g m

/-- The bundled original-section formula determines a sheaf morphism uniquely. -/
lemma hom_ext {P : (Spec S).Modules}
    (a b : (pullback (Spec.map φ)).obj (tilde M) ⟶ P)
    (h : ∀ m : M, moduleSpecΓFunctor.map a (unit φ M m) =
      moduleSpecΓFunctor.map b (unit φ M m)) : a = b :=
  AffineTildePullbackMap.hom_ext φ M a b h

end FLT.Mazur.AffineTildePullbackSectionMap
