/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalDescentData

/-!
# Original-overlap recognition makes reconstruction a descent morphism

A recovery identifying the original overlap with its canonical chart overlap
is a compatible map from the canonical pullback datum to the original datum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules}
variable (D : Data p M) (A : X.Modules) (e : (pullback p).obj A ≅ M)

/-- Original-overlap recognition supplies the actual recovery compatibility square. -/
lemma canonical_recovery_compatible
    (he : D.overlap = chartOverlap p (Limits.pullback.fst p p)
      (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
      rfl Limits.pullback.condition.symm A e) :
    (canonical p A).MapCompatible p D e.hom := by
  unfold Data.MapCompatible
  rw [he]
  simp only [canonical, chartOverlap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, ← Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

end FLT.Mazur.SchemeGeometricDescent
