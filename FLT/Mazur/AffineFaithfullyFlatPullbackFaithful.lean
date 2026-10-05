/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleCoalgebraDescent

/-!
# Faithfulness of affine faithfully flat pullback on tilde sheaves

Effective module descent detects coefficient maps. Naturality of the tilde
pullback comparison then detects arbitrary sheaf maps between tilde objects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineFaithfullyFlatPullbackFaithful
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)

include hφ

/-- Faithfully flat scalar extension detects equality of coefficient maps. -/
theorem extendScalars_map_injective {M N : ModuleCat.{u} R} (f g : M ⟶ N)
    (h : (ModuleCat.extendScalars φ.hom).map f = (ModuleCat.extendScalars φ.hom).map g) :
    f = g := by
  apply (AffineModuleCoalgebraDescent.descentEquivalence φ hφ).functor.map_injective
  apply Comonad.Coalgebra.Hom.ext
  exact h

/-- Pullback detects arbitrary morphisms between tilde sheaves. -/
theorem tilde_map_injective {M N : ModuleCat.{u} R} (f g : tilde M ⟶ tilde N)
    (h : (pullback (Spec.map φ)).map f = (pullback (Spec.map φ)).map g) : f = g := by
  let a := (tilde.functor R).preimage f
  let b := (tilde.functor R).preimage g
  have hn (k : M ⟶ N) :
      (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map k) ≫
          (AffineModulePullbackSections.tildePullbackIso φ).hom.app N =
        (AffineModulePullbackSections.tildePullbackIso φ).hom.app M ≫
          (pullback (Spec.map φ)).map ((tilde.functor R).map k) :=
    (AffineModulePullbackSections.tildePullbackIso φ).hom.naturality k
  have hh : (pullback (Spec.map φ)).map ((tilde.functor R).map a) =
      (pullback (Spec.map φ)).map ((tilde.functor R).map b) := by
    simpa only [a, b, Functor.map_preimage] using h
  have hab : a = b := by
    apply extendScalars_map_injective φ hφ
    apply (tilde.functor S).map_injective
    apply (cancel_mono ((AffineModulePullbackSections.tildePullbackIso φ).hom.app N)).mp
    exact (hn a).trans ((congrArg
      ((AffineModulePullbackSections.tildePullbackIso φ).hom.app M ≫ ·) hh).trans (hn b).symm)
  calc
    f = (tilde.functor R).map a := (Functor.map_preimage (tilde.functor R) f).symm
    _ = (tilde.functor R).map b := congrArg (tilde.functor R).map hab
    _ = g := Functor.map_preimage (tilde.functor R) g

end FLT.Mazur.AffineFaithfullyFlatPullbackFaithful
