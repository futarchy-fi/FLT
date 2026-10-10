/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardPresheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Total spaces under change of the fixed Picard base

For S' → S and T → S', the actual iterated fiber product is canonically
isomorphic to X ×[S] T. This comparison is natural in T over the new base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S S' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S)

/-- Flatten the fiber product after changing the fixed base from S to S'. -/
def relativeBaseChangeTotalIso (T : Over S') :
    Limits.pullback (Limits.pullback.snd f a) T.hom ≅
      Limits.pullback f ((Over.map a).obj T).hom :=
  pullbackLeftPullbackSndIso f a T.hom

/-- Flattening leaves the test scheme unchanged. -/
@[reassoc (attr := simp)]
lemma relativeBaseChangeTotalIso_hom_snd (T : Over S') :
    (relativeBaseChangeTotalIso f a T).hom ≫ Limits.pullback.snd f (T.hom ≫ a) =
      Limits.pullback.snd _ _ := pullbackLeftPullbackSndIso_hom_snd f a T.hom

/-- The inverse comparison also leaves the test scheme unchanged. -/
@[reassoc (attr := simp)]
lemma relativeBaseChangeTotalIso_inv_snd (T : Over S') :
    (relativeBaseChangeTotalIso f a T).inv ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ := pullbackLeftPullbackSndIso_inv_snd_snd f a T.hom

/-- The actual total-space comparison is natural in the test scheme over the new base. -/
@[reassoc]
lemma relativeBaseChangeTotalIso_naturality {T U : Over S'} (g : T ⟶ U) :
    relativeTotalMap (Limits.pullback.snd f a) g ≫ (relativeBaseChangeTotalIso f a U).hom =
      (relativeBaseChangeTotalIso f a T).hom ≫ relativeTotalMap f ((Over.map a).map g) := by
  apply Limits.pullback.hom_ext <;>
    simp [relativeBaseChangeTotalIso, relativeTotalMap, Category.assoc]

end FLT.Mazur.SchemePicard
