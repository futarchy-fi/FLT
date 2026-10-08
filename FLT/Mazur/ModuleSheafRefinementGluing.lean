/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomComparison
public import FLT.Mazur.ModuleSheafMorphismRefinement
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Gluing compatibility from geometric common refinements

Pullback maps are compatible on entire intersections when their refinements
agree on a covering family of smaller charts. This converts geometric
comparison equations directly into the compatibility consumed by gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u v w

namespace FLT.Mazur.ModuleSheafOpenImmersionGluing

open ModuleSheafOpenImmersionLocalHom AffineIteratedPullbackSections

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v}
variable (Y : ι → Scheme.{u}) (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, (pullback (i j)).obj M ⟶ (pullback (i j)).obj N)

/-- Geometric refinement equations on covering common charts imply gluing compatibility. -/
lemma compatible_of_geometric_refinements
    (κ : ι → ι → Type w) (Z : ∀ j k, κ j k → Scheme.{u})
    (d : ∀ j k l, Z j k l ⟶ X) [∀ j k l, IsOpenImmersion (d j k l)]
    (left : ∀ j k l, Z j k l ⟶ Y j) [∀ j k l, IsOpenImmersion (left j k l)]
    (right : ∀ j k l, Z j k l ⟶ Y k) [∀ j k l, IsOpenImmersion (right j k l)]
    (hl : ∀ j k l, left j k l ≫ i j = d j k l)
    (hr : ∀ j k l, right j k l ≫ i k = d j k l)
    (hcover : ∀ j k (x : X), x ∈ (i j).opensRange ⊓ (i k).opensRange →
      ∃ l, x ∈ (d j k l).opensRange)
    (b : ∀ j k l, (pullback (d j k l)).obj M ⟶ (pullback (d j k l)).obj N)
    (ha : ∀ j k l,
      (pullback (left j k l)).map (a j) ≫
          (compositeIso (left j k l) (i j) (d j k l) (hl j k l) N).hom =
        (compositeIso (left j k l) (i j) (d j k l) (hl j k l) M).hom ≫ b j k l)
    (hb : ∀ j k l,
      (pullback (right j k l)).map (a k) ≫
          (compositeIso (right j k l) (i k) (d j k l) (hr j k l) N).hom =
        (compositeIso (right j k l) (i k) (d j k l) (hr j k l) M).hom ≫ b j k l) :
    Compatible Y i a := by
  apply ModuleSheafMorphismGluing.compatible_of_refinement_covers
    (fun j ↦ (i j).opensRange) (fun j ↦ localHom (i j) (a j)) κ
    (fun j k l ↦ (d j k l).opensRange)
    (fun j k l ↦ refinementRange_le_of_eq (i j) (left j k l) (d j k l) (hl j k l))
    (fun j k l ↦ refinementRange_le_of_eq (i k) (right j k l) (d j k l) (hr j k l))
    hcover
  intro j k l T hT
  exact (localHom_refine_of_eq (i j) (left j k l) (d j k l) (hl j k l)
    (a j) (b j k l) (ha j k l) T hT _).symm.trans
      (localHom_refine_of_eq (i k) (right j k l) (d j k l) (hr j k l)
        (a k) (b j k l) (hb j k l) T hT _)

end FLT.Mazur.ModuleSheafOpenImmersionGluing
