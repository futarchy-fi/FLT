/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionDiagramGluing
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Gluing an affine algebra intersection diagram over its base

A compatible family of algebra maps defines a genuine functor. Its spectrum
diagram glues when the restriction maps are open immersions and the union
squares are cartesian. The structural maps glue as well, giving a scheme
over the same coefficient ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

/-- Package algebra maps with their proven identity and composition laws as a functor. -/
def algebraDiagramOfHoms {S : Type u} [CommRing S]
    {J : Type v} [Category J] (B : J → Type u)
    [∀ a, CommRing (B a)] [∀ a, Algebra S (B a)]
    (φ : ∀ {a b}, (a ⟶ b) → (B a →ₐ[S] B b))
    (hid : ∀ a, φ (𝟙 a) = AlgHom.id S _)
    (hcomp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), φ (f ≫ g) = (φ g).comp (φ f)) :
    J ⥤ CommAlgCat S where
  obj a := .of S (B a)
  map f := CommAlgCat.ofHom (φ f)
  map_id a := CommAlgCat.Hom.ext (hid a)
  map_comp f g := CommAlgCat.Hom.ext (hcomp f g)

variable {S : Type u} [CommRing S] {ι : Type v}
  (C : NonemptyChartSet ι ⥤ CommAlgCat S)

/-- The contravariant spectrum diagram of intersection algebras. -/
def affineIntersectionSchemeDiagram : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u} :=
  (C ⋙ forget₂ (CommAlgCat S) CommRingCat).op ⋙ Scheme.Spec

/-- The structural maps of an algebra diagram form a cocone to its affine base. -/
def affineIntersectionBaseCocone : Cocone (affineIntersectionSchemeDiagram C) where
  pt := Spec (.of S)
  ι.app a := Spec.map (CommRingCat.ofHom (algebraMap S (C.obj a.unop)))
  ι.naturality {a b} f := by
    change Spec.map (CommRingCat.ofHom (C.map f.unop).hom.toRingHom) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext ((C.map f.unop).hom.comp_algebraMap)

variable [Finite ι]
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f).hom.toRingHom))]
  (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (C.map (homOfLE hrt)).hom.toRingHom)))

/-- Glue an affine intersection algebra diagram over its coefficient ring. -/
def affineIntersectionGlueData : Scheme.GlueData.{u} := by
  letI : ∀ {i j} (f : i ⟶ j), IsOpenImmersion ((affineIntersectionSchemeDiagram C).map f) :=
    fun {_ _} f ↦ inferInstanceAs
      (IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f.unop).hom.toRingHom)))
  exact intersectionDiagramGlueData (affineIntersectionSchemeDiagram C) hp

/-- The structural maps glue to a morphism from the constructed scheme to `Spec S`. -/
def affineIntersectionGluedToBase : (affineIntersectionGlueData C hp).glued ⟶ Spec (.of S) := by
  letI : ∀ {i j} (f : i ⟶ j), IsOpenImmersion ((affineIntersectionSchemeDiagram C).map f) :=
    fun {_ _} f ↦ inferInstanceAs
      (IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f.unop).hom.toRingHom)))
  letI := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram C) hp
  exact (Scheme.IsLocallyDirected.isColimit (affineIntersectionSchemeDiagram C)).desc
    (affineIntersectionBaseCocone C)

end FLT.Mazur.Approximation
