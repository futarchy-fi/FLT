/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Sections and points of schemes over a base

Sections and ring-valued points are morphisms in `Over S`, so they retain their
specified map to the base. Restricting a section along `T ⟶ S` means precomposing
with that map; it does not require constructing a fiber product.

`Sections.restrict_map` expresses the commutative section diagram used in Mazur,
*Modular curves and the Eisenstein ideal* (1977), III §5, pp. 159–160. Its equality
is in the over category. The corresponding `_left` lemmas expose scheme morphisms,
including their structure-map equations. No arithmetic hypotheses are needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

/-- Sections of a scheme over `S`, with the section equation included. -/
abbrev Sections {S : Scheme.{u}} (X : Over S) := Over.mk (𝟙 S) ⟶ X

/-- Ring-valued points with a specified map from the spectrum to the base. -/
abbrev Points {S : Scheme.{u}} (X : Over S) {K : Type u} [CommRing K]
    (s : Spec (CommRingCat.of K) ⟶ S) := Over.mk s ⟶ X

namespace Sections

variable {S T : Scheme.{u}} {X Y Z : Over S}

/-- Postcompose a section with a morphism over the base. -/
def map (f : X ⟶ Y) (x : Sections X) : Sections Y := x ≫ f

@[simp]
theorem map_left (f : X ⟶ Y) (x : Sections X) :
    (map f x).left = x.left ≫ f.left := rfl

@[simp]
theorem map_id (x : Sections X) : map (𝟙 X) x = x := Category.comp_id x

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Sections X) :
    map (f ≫ g) x = map g (map f x) := (Category.assoc x f g).symm

/-- Restrict a section along any scheme morphism to its base. For an affine
source this is a `Points X s`, including its equation over the base. -/
def restrict (s : T ⟶ S) (x : Sections X) : Over.mk s ⟶ X :=
  (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x

@[simp]
theorem restrict_left (s : T ⟶ S) (x : Sections X) :
    (restrict s x).left = s ≫ x.left := rfl

/-- The restricted morphism still lies over the specified base map. -/
theorem restrict_left_hom (s : T ⟶ S) (x : Sections X) :
    (restrict s x).left ≫ X.hom = s := Over.w (restrict s x)

@[simp]
theorem restrict_id (x : Sections X) : restrict (𝟙 S) x = x := by
  apply Over.OverMorphism.ext
  simp

/-- Restriction commutes with postcomposition as an equality of over-morphisms. -/
@[simp]
theorem restrict_map (s : T ⟶ S) (f : X ⟶ Y) (x : Sections X) :
    restrict s (map f x) = restrict s x ≫ f :=
  (Category.assoc _ x f).symm

/-- Both paths in the section diagram have the same underlying scheme morphism. -/
theorem restrict_map_left (s : T ⟶ S) (f : X ⟶ Y) (x : Sections X) :
    (restrict s (map f x)).left = (s ≫ x.left) ≫ f.left :=
  (Category.assoc s x.left f.left).symm

/-- Equality after restriction is preserved by any morphism over the base. -/
theorem map_restrict_eq (s : T ⟶ S) (f : X ⟶ Y) {x y : Sections X}
    (h : restrict s x = restrict s y) : restrict s (map f x) = restrict s (map f y) := by
  simpa only [restrict_map] using congrArg (fun z => z ≫ f) h

end Sections

namespace Points

variable {S : Scheme.{u}} {X Y Z : Over S}
variable {K L : Type u} [CommRing K] [CommRing L]
variable {s : Spec (CommRingCat.of K) ⟶ S}

/-- Postcompose a ring-valued point with a morphism over the base. -/
def map (f : X ⟶ Y) (x : Points X s) : Points Y s := x ≫ f

@[simp]
theorem map_left (f : X ⟶ Y) (x : Points X s) :
    (map f x).left = x.left ≫ f.left := rfl

@[simp]
theorem map_id (x : Points X s) : map (𝟙 X) x = x := Category.comp_id x

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X s) :
    map (f ≫ g) x = map g (map f x) := (Category.assoc x f g).symm

/-- Precompose a point along a morphism of spectra, composing its base map too. -/
def precomp (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : Points X s) : Points X (a ≫ s) :=
  (Over.homMk a : Over.mk (a ≫ s) ⟶ Over.mk s) ≫ x

@[simp]
theorem precomp_left (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : Points X s) : (precomp a x).left = a ≫ x.left := rfl

theorem precomp_left_hom (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : Points X s) : (precomp a x).left ≫ X.hom = a ≫ s := Over.w (precomp a x)

/-- Changing the spectrum of a point commutes with a morphism over the base. -/
@[simp]
theorem precomp_map (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (x : Points X s) : precomp a (map f x) = map f (precomp a x) :=
  (Category.assoc _ x f).symm

/-- Restriction along a composite agrees with precomposition of the restricted point. -/
@[simp]
theorem precomp_restrict (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (s : Spec (CommRingCat.of K) ⟶ S) (x : Sections X) :
    precomp a (Sections.restrict s x) = Sections.restrict (a ≫ s) x := by
  apply Over.OverMorphism.ext
  exact (Category.assoc a s x.left).symm

/-- The ring-valued version of the section diagram, with both sides typed as points. -/
theorem map_restrict (f : X ⟶ Y) (s : Spec (CommRingCat.of K) ⟶ S)
    (x : Sections X) : map f (Sections.restrict s x) = Sections.restrict s (Sections.map f x) :=
  (Sections.restrict_map s f x).symm

end Points

end FLT.Mazur
