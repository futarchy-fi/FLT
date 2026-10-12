/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric base tests detect equality of underlying point maps

A residue-field geometric point of the original source lifts to its actual
base pullback. Equality there gives equality at the original source point.
This only asserts equality of point maps, not scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} {X Y : Over S}

/-- Equality on geometric base changes detects the original underlying point maps. -/
theorem pointwise_eq_of_geometric_pullback (a b : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S),
      (Over.pullback g).map a = (Over.pullback g).map b) (x : X.left) :
    a.left x = b.left x := by
  let K := AlgebraicClosure (X.left.residueField x)
  let p : Spec (.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) K)) ≫
      X.left.fromSpecResidueField x
  let g := p ≫ X.hom
  let l : Spec (.of K) ⟶ pullback X.hom g :=
    pullback.lift p (𝟙 _) (Category.id_comp _).symm
  have he := congrArg (fun k ↦ l ≫ k.left ≫ pullback.fst Y.hom g) (h K g)
  have hp : p ≫ a.left = p ≫ b.left := by
    simpa only [Over.pullback_map_left, pullback.lift_fst, ← Category.assoc, l] using he
  have hx : p (IsLocalRing.closedPoint K) = x :=
    X.left.fromSpecResidueField_apply x _
  have hh := congrArg (fun k : Spec (.of K) ⟶ Y.left ↦ k (IsLocalRing.closedPoint K)) hp
  change a.left (p _) = b.left (p _) at hh
  rwa [hx] at hh

end FLT.Mazur.FCurve
