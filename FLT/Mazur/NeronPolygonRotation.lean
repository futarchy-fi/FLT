/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingRotation
public import FLT.Mazur.NeronPolygonPredicate

/-!
# Rotations of a realized Néron polygon

A specified pushout cocone of the cyclic pinching span carries rotations
induced from its normalization and nodes. This uses only that cocone's
universal property, without a global pushout-existence instance. Rotation
by the negative residue supplies an inverse, preserving the chosen marking.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable (K : Type u) [Field K] {n : ℕ} [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (CommRingCat.of K))}
variable (p : components K n ⟶ C) (q : nodes K n ⟶ C)
variable (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Descend the rotation of the cyclic span to its specified realization. -/
def polygonRotation (a : ZMod n) : C ⟶ C :=
  h.desc (componentsRotation K a ≫ p) (nodesRotation K a ≫ q) (by
    rw [← Category.assoc, ← rotation_toComponents, Category.assoc, h.w,
      ← Category.assoc, rotation_toNodes, Category.assoc])

@[reassoc (attr := simp)]
theorem components_polygonRotation (a : ZMod n) :
    p ≫ polygonRotation K hn p q h a = componentsRotation K a ≫ p := by
  simp [polygonRotation]

@[reassoc (attr := simp)]
theorem nodes_polygonRotation (a : ZMod n) :
    q ≫ polygonRotation K hn p q h a = nodesRotation K a ≫ q := by
  simp [polygonRotation]

@[simp]
theorem polygonRotation_zero : polygonRotation K hn p q h 0 = 𝟙 C := by
  apply h.hom_ext <;> simp

theorem polygonRotation_add (a b : ZMod n) :
    polygonRotation K hn p q h (a + b) =
      polygonRotation K hn p q h a ≫ polygonRotation K hn p q h b := by
  apply h.hom_ext <;> simp [componentsRotation_add, nodesRotation_add, Category.assoc]

/-- Rotation is an automorphism, with inverse rotation by the negative residue. -/
def polygonRotationIso (a : ZMod n) : C ≅ C where
  hom := polygonRotation K hn p q h a
  inv := polygonRotation K hn p q h (-a)
  hom_inv_id := by rw [← polygonRotation_add, add_neg_cancel, polygonRotation_zero]
  inv_hom_id := by rw [← polygonRotation_add, neg_add_cancel, polygonRotation_zero]

@[simp]
theorem polygonRotationIso_hom (a : ZMod n) :
    (polygonRotationIso K hn p q h a).hom = polygonRotation K hn p q h a := rfl

@[simp]
theorem polygonRotationIso_inv (a : ZMod n) :
    (polygonRotationIso K hn p q h a).inv = polygonRotation K hn p q h (-a) := rfl

end FLT.Mazur.PolygonPinching
