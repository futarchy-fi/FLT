/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineAmbientTestRefinement

/-!
# Refining ambient projection equations

A projection equation involving the effective ambient comparison persists
on any scheme test mapping to the original one. Endpoint normalization is
kept explicit, so this applies to independently chosen chart coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W Z : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf ambientTestComparison

/-- Ambient comparison refinement retains independently specified endpoint maps. -/
@[reassoc]
lemma ambientTestComparison_refine_eq (t : Z ⟶ W) (a : W ⟶ X) (a' : Z ⟶ X)
    (ha : t ≫ a = a') (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (i' : Z ⟶ Spec C.baseRing) (j' : Z ⟶ Spec C'.baseRing)
    (ei : t ≫ i = i') (ej : t ≫ j = j')
    (hi' : i' ≫ C.base = a') (hj' : j' ≫ C'.base = a') :
    (pullback t).map (C.ambientTestComparison C' D a i j hi hj) ≫
        (SheafPullbackPathComparison.comparison t a a' ha).hom.app
          ((pushforward C'.base).obj (C'.sheaf D)) =
      (SheafPullbackPathComparison.comparison t a a' ha).hom.app
        ((pushforward C.base).obj (C.sheaf D)) ≫
        C.ambientTestComparison C' D a' i' j' hi' hj' := by
  subst a' i' j'
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl] using
    C.ambientTestComparison_refine C' D t a i j hi hj

/-- An actual ambient projection equation pulls back to every further scheme test. -/
lemma ambientProjection_refine {G : X.Modules}
    (q : G ⟶ (pushforward C.base).obj (C.sheaf D))
    (q' : G ⟶ (pushforward C'.base).obj (C'.sheaf D))
    (t : Z ⟶ W) (a : W ⟶ X) (a' : Z ⟶ X) (ha : t ≫ a = a')
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (i' : Z ⟶ Spec C.baseRing) (j' : Z ⟶ Spec C'.baseRing)
    (ei : t ≫ i = i') (ej : t ≫ j = j')
    (hi' : i' ≫ C.base = a') (hj' : j' ≫ C'.base = a')
    (hq : (pullback a).map q ≫ C.ambientTestComparison C' D a i j hi hj =
      (pullback a).map q') :
    (pullback a').map q ≫ C.ambientTestComparison C' D a' i' j' hi' hj' =
      (pullback a').map q' := by
  apply (cancel_epi ((SheafPullbackPathComparison.comparison t a a' ha).hom.app G)).mp
  have hn := (SheafPullbackPathComparison.comparison t a a' ha).hom.naturality q
  have hn' := (SheafPullbackPathComparison.comparison t a a' ha).hom.naturality q'
  dsimp only [Functor.comp_map] at hn hn'
  rw [← Category.assoc, ← hn, Category.assoc,
    ← ambientTestComparison_refine_eq C C' D t a a' ha
    i j hi hj i' j' ei ej hi' hj', ← Functor.map_comp_assoc, hq, hn']

end FLT.Mazur.SchemeAffineDescent.Chart
