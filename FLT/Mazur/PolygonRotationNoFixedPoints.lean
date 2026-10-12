/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonRotationAction
public import FLT.Mazur.PolygonNodeIncidence
public import FLT.Mazur.PolygonNodeLocus

/-!
# Nonidentity rotations have no fixed points on the original polygon

The Laurent components are disjoint and the node labels are distinct.
Rotation shifts both sets of labels, so no point can remain fixed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- A nonzero cyclic shift fixes no original label. -/
theorem rotateIndex_ne_self (a : ZMod n) (ha : a ≠ 0) (i : Fin n) :
    rotateIndex a i ≠ i := by
  intro he
  apply ha
  have hz := congrArg (ZMod.finEquiv n) he
  simpa [rotateIndex] using hz

/-- The actual pinching rotation has no fixed point for a nonidentity label. -/
theorem polygonRotation_ne_self (a : ZMod n) (ha : a ≠ 0) (x : C.left) :
    (polygonRotation K hn p q h a).left x ≠ x := by
  let _ := polygon_lfp K n hn p q h
  intro hf
  by_cases hx : x ∈ C.hom.smoothLocus
  · change x ∈ (C.hom.smoothLocus : Set C.left) at hx
    rw [smooth_range K n hn p q h] at hx
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
    have hr : (polygonRotation K hn p q h a).left
        ((torusToComponent K ≫ componentι K n i ≫ p).left t) =
          (torusToComponent K ≫ componentι K n (rotateIndex a i) ≫ p).left t := by
      exact congrArg (fun f ↦ f.left t)
        (congrArg (fun f ↦ torusToComponent K ≫ f)
          (componentι_polygonRotation K hn p q h a i))
    have hd := PolygonComponentDistinct.torus_disjoint K n hn p q h
      (rotateIndex_ne_self n a ha i)
    exact Set.disjoint_left.mp hd ⟨t, hr.symm.trans hf⟩ ⟨t, rfl⟩
  · obtain ⟨i, t, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K n hn p q h x).mp hx
    have hr : (polygonRotation K hn p q h a).left ((nodeι K n i ≫ q).left t) =
        (nodeι K n (rotateIndex a i) ≫ q).left t :=
      congrArg (fun f ↦ f.left t) (nodeι_polygonRotation K hn p q h a i)
    exact rotateIndex_ne_self n a ha i
      ((PolygonNodeIncidence.node_eq_iff K n hn p q h _ _ t t).mp (hr.symm.trans hf))

end FLT.Mazur.PolygonPinching
