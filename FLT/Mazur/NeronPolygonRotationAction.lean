/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonRotation

/-!
# The natural cyclic action on polygon points

Postcomposition with polygon rotations acts on points over every test scheme.
The action commutes with change of test scheme and rotates the marked
normalization components and nodes, as in DR II.1.12(c). This makes no claim
identifying these markings with irreducible components or with translations
by points of a smooth group scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable (K : Type u) [Field K] {n : ℕ} [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (CommRingCat.of K))}
variable (p : components K n ⟶ C) (q : nodes K n ⟶ C)
variable (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Rotate a point with values in any scheme over the base. -/
def rotatePoint (a : ZMod n) {U : Over (Spec (CommRingCat.of K))}
    (x : U ⟶ C) : U ⟶ C := x ≫ polygonRotation K hn p q h a

@[simp]
theorem rotatePoint_zero {U : Over (Spec (CommRingCat.of K))} (x : U ⟶ C) :
    rotatePoint K hn p q h 0 x = x := by
  simp [rotatePoint]

theorem rotatePoint_add (a b : ZMod n)
    {U : Over (Spec (CommRingCat.of K))} (x : U ⟶ C) :
    rotatePoint K hn p q h (a + b) x =
      rotatePoint K hn p q h b (rotatePoint K hn p q h a x) := by
  simp [rotatePoint, polygonRotation_add, Category.assoc]

/-- The action is natural in the scheme of values. -/
theorem rotatePoint_precomp (a : ZMod n)
    {U V : Over (Spec (CommRingCat.of K))} (v : V ⟶ U) (x : U ⟶ C) :
    rotatePoint K hn p q h a (v ≫ x) = v ≫ rotatePoint K hn p q h a x := by
  simp [rotatePoint, Category.assoc]

@[reassoc]
theorem componentι_polygonRotation (a : ZMod n) (i : Fin n) :
    componentι K n i ≫ p ≫ polygonRotation K hn p q h a =
      componentι K n (rotateIndex a i) ≫ p := by
  simp

@[reassoc]
theorem nodeι_polygonRotation (a : ZMod n) (i : Fin n) :
    nodeι K n i ≫ q ≫ polygonRotation K hn p q h a =
      nodeι K n (rotateIndex a i) ≫ q := by
  simp

/-- Rotation by the negative residue undoes rotation on every point. -/
@[simp]
theorem rotatePoint_neg_rotatePoint (a : ZMod n)
    {U : Over (Spec (CommRingCat.of K))} (x : U ⟶ C) :
    rotatePoint K hn p q h (-a) (rotatePoint K hn p q h a x) = x := by
  rw [← rotatePoint_add, add_neg_cancel, rotatePoint_zero]

/-- Each rotation is a permutation of the points over any test scheme. -/
theorem rotatePoint_bijective (a : ZMod n) {U : Over (Spec (CommRingCat.of K))} :
    Function.Bijective (rotatePoint K hn p q h a : (U ⟶ C) → (U ⟶ C)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨rotatePoint K hn p q h (-a), ?_, ?_⟩
  · intro x
    exact rotatePoint_neg_rotatePoint K hn p q h a x
  · intro x
    rw [← rotatePoint_add, neg_add_cancel, rotatePoint_zero]

end FLT.Mazur.PolygonPinching
