/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Actual affine pullback detects scalar-extension nonvanishing

Naturality of the tilde pullback comparison identifies the actual geometric
map with the scalar-extended module map, including whether either is zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.AffineTildePullbackNonvanishing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) {M N : ModuleCat.{u} R} (f : M ⟶ N)

/-- Zero is detected by the original scalar-extension map. -/
lemma map_eq_zero_iff :
    (pullback (Spec.map φ)).map ((tilde.functor R).map f) = 0 ↔
      (ModuleCat.extendScalars φ.hom).map f = 0 := by
  let e := AffineModulePullbackSections.tildePullbackIso φ
  have hn := e.hom.naturality f
  change (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map f) ≫ e.hom.app N =
    e.hom.app M ≫ (pullback (Spec.map φ)).map ((tilde.functor R).map f) at hn
  constructor
  · intro h
    apply (tilde.functor S).map_injective
    rw [Functor.map_zero]
    apply (cancel_mono (e.hom.app N)).mp
    rw [hn, h, comp_zero, zero_comp]
  · intro h
    apply (cancel_epi (e.hom.app M)).mp
    rw [← hn, h, Functor.map_zero, zero_comp, comp_zero]

/-- Nonzero geometric pullback is exactly nonzero scalar extension. -/
lemma map_ne_zero_iff :
    (pullback (Spec.map φ)).map ((tilde.functor R).map f) ≠ 0 ↔
      (ModuleCat.extendScalars φ.hom).map f ≠ 0 := not_congr (map_eq_zero_iff φ f)

end FLT.Mazur.AffineTildePullbackNonvanishing
