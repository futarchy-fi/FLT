/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeOpenUnion

/-!
# Gluing relative maps on an actual open union

Compatibility on the original members constructs a unique relative map
from their scheme-theoretic union, with its original ambient inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOpenUnion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {T : Over S} {ι : Type} {U : ι → Over S}
  (a : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (a i).left]
  {Y : Over S} (b : ∀ i, U i ⟶ Y)
  (hb : ∀ i j {W : Over S} (p : W ⟶ U i) (q : W ⟶ U j),
    p ≫ a i = q ≫ a j → p ≫ b i = q ≫ b j)

include hb in
/-- Relative compatibility gives compatibility on the actual scheme intersections. -/
theorem maps_compatible (i j : ι) :
    pullback.fst ((chart a i).left) ((chart a j).left) ≫ (b i).left =
      pullback.snd ((chart a i).left) ((chart a j).left) ≫ (b j).left := by
  let W : Over S := Over.mk
    (pullback.fst ((chart a i).left) ((chart a j).left) ≫ (U i).hom)
  let p : W ⟶ U i := Over.homMk (pullback.fst _ _) rfl
  let q : W ⟶ U j := Over.homMk (pullback.snd _ _) (by
    rw [← (chart a j).w, ← Category.assoc, ← pullback.condition,
      Category.assoc, (chart a i).w]
    rfl)
  have h : p ≫ chart a i = q ≫ chart a j := Over.OverMorphism.ext pullback.condition
  have ha : p ≫ a i = q ≫ a j := by
    rw [← chart_inclusion a i, ← chart_inclusion a j, ← Category.assoc,
      ← Category.assoc, h]
  exact congrArg Over.Hom.left (hb i j p q ha)

/-- The actual scheme gluing respects the original structure map. -/
def glue : test a ⟶ Y := by
  let k := (cover a).glueMorphisms (fun i ↦ (b i).left) (maps_compatible a b hb)
  refine Over.homMk k ?_
  apply (cover a).hom_ext
  intro i
  change (chart a i).left ≫ k ≫ Y.hom = (chart a i).left ≫ (test a).hom
  have hk : (chart a i).left ≫ k = (b i).left :=
    (cover a).ι_glueMorphisms _ _ i
  rw [← Category.assoc, hk, Over.w, Over.w]

theorem chart_glue (i : ι) : chart a i ≫ glue a b hb = b i := by
  apply Over.OverMorphism.ext
  change (cover a).f i ≫ (cover a).glueMorphisms
    (fun j ↦ (b j).left) (maps_compatible a b hb) = (b i).left
  exact (cover a).ι_glueMorphisms _ _ i

/-- The original member maps characterize the relative glued map uniquely. -/
theorem glue_unique (k : test a ⟶ Y) (hk : ∀ i, chart a i ≫ k = b i) :
    k = glue a b hb := by
  apply Over.OverMorphism.ext
  apply (cover a).hom_ext
  intro i
  exact congrArg Over.Hom.left ((hk i).trans (chart_glue a b hb i).symm)

end FLT.Mazur.RelativeOpenUnion
