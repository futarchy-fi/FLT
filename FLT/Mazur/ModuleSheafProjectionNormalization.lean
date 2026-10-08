/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Projection equations under normalized pullback

An equation between pulled-back global projections survives further pullback
and the canonical change from an iterated path to its composite.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackMapNormalization

open SheafPullbackPathComparison

/-- Normalizing a further pullback preserves equations between global projections. -/
lemma normalize_projection {X O W : Scheme.{u}} (c : W ⟶ O) (i : O ⟶ X)
    (r : W ⟶ X) (h : c ≫ i = r) {M N P : X.Modules}
    (p : M ⟶ N) (q : M ⟶ P) (a : (pullback i).obj N ⟶ (pullback i).obj P)
    (ha : (pullback i).map p ≫ a = (pullback i).map q) :
    (pullback r).map p ≫ normalize c i i r r h h a = (pullback r).map q := by
  apply (cancel_epi ((comparison c i r h).hom.app M)).mp
  rw [← Category.assoc, ← (comparison c i r h).hom.naturality p, Category.assoc]
  rw [normalize_comm]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, ha]
  exact (comparison c i r h).hom.naturality q

end FLT.Mazur.SheafPullbackMapNormalization
