/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Normalizing an iterated pullback of a morphism

Naturality of path comparison identifies a normalized iterated pullback
with the pullback along the named composite map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackMapNormalization
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U Y : Scheme.{u}}

/-- Normalization recovers the direct pullback of an original morphism. -/
lemma normalize_pullback_map (t : T ⟶ U) (b : U ⟶ Y) (d : T ⟶ Y) (hd : t ≫ b = d)
    {M N : Y.Modules} (f : M ⟶ N) :
    normalize t b b d d hd hd ((pullback b).map f) = (pullback d).map f := by
  apply (cancel_epi ((comparison t b d hd).hom.app M)).mp
  rw [normalize_comm]
  exact (comparison t b d hd).hom.naturality f

end FLT.Mazur.SheafPullbackMapNormalization
