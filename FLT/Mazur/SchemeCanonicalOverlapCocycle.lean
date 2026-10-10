/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalOverlapLaws
public import FLT.Mazur.SchemeOverlapCocycleChart

/-!
# The cocycle law for canonical pullback overlaps

On a triple test, normalize all three pair overlaps over the same base map.
The cocycle follows from cancellation of the middle pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SchemeOverlapCocycleChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z T : Scheme.{u}}

/-- Canonical pullback overlaps satisfy the cocycle on every compatible triple test. -/
lemma overlap_cocycle (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k)
    (p12 p23 p13 : T ⟶ Z) (c1 c2 c3 : T ⟶ Y)
    (w12l : p12 ≫ l = c1) (w12r : p12 ≫ r = c2)
    (w23l : p23 ≫ l = c2) (w23r : p23 ≫ r = c3)
    (w13l : p13 ≫ l = c1) (w13r : p13 ≫ r = c3)
    (A : X.Modules) :
    CocycleCompatible l r p12 p23 p13 c1 c2 c3 w12l w12r w23l w23r w13l w13r
      ((pullback p).obj A) (overlap p l r k hl hr A) := by
  have h2 : c2 ≫ p = c1 ≫ p := by
    rw [← w12r, ← w12l, Category.assoc, Category.assoc, hl, hr]
  have h3 : c3 ≫ p = c1 ≫ p := by
    rw [← w13r, ← w13l, Category.assoc, Category.assoc, hl, hr]
  unfold CocycleCompatible
  rw [normalize_overlap_base p l r k hl hr p12 c1 c2 w12l w12r (c1 ≫ p) rfl h2,
    normalize_overlap_base p l r k hl hr p23 c2 c3 w23l w23r (c1 ≫ p) h2 h3,
    normalize_overlap_base p l r k hl hr p13 c1 c3 w13l w13r (c1 ≫ p) rfl h3]
  exact overlap_trans p c1 c2 c3 (c1 ≫ p) rfl h2 h3 A

end FLT.Mazur.SchemePullbackOverlap
