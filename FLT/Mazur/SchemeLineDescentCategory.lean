/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentMapLaws
public import FLT.Mazur.SchemePicardClasses

/-!
# The category of geometric line-bundle descent data

Objects carry an actual line bundle and its geometric descent datum. Morphisms
are precisely the sheaf maps intertwining the original overlap isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Actual rank-one geometric descent data for a fixed scheme morphism. -/
structure LineData where
  /-- The sheaf on the covering scheme. -/
  obj : Y.Modules
  /-- The covering sheaf is a line bundle. -/
  rankOne : LocallyFreeRankOne obj
  /-- The original diagonal and cocycle descent data. -/
  datum : Data p obj

namespace LineData

/-- Morphisms retain compatibility with the original descent overlap. -/
abbrev Hom (D E : LineData p) := {f : D.obj ⟶ E.obj // D.datum.MapCompatible p E.datum f}

instance : Category (LineData p) where
  Hom := Hom p
  id D := ⟨𝟙 D.obj, D.datum.mapCompatible_id⟩
  comp f g := ⟨f.val ≫ g.val, Data.mapCompatible_comp _ _ _ _ _ f.property g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- Equality of descent morphisms is equality of their sheaf maps. -/
@[ext]
lemma hom_ext {D E : LineData p} {f g : D ⟶ E} (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- Forget the descent datum while retaining its original source sheaf. -/
def forget : LineData p ⥤ Y.Modules where
  obj D := D.obj
  map f := f.val

/-- A compatible sheaf isomorphism is an isomorphism of geometric line descent data. -/
def isoMk {D E : LineData p} (e : D.obj ≅ E.obj)
    (he : D.datum.MapCompatible p E.datum e.hom) : D ≅ E where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, D.datum.mapCompatible_inv E.datum e he⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

end LineData
end FLT.Mazur.SchemeGeometricDescent
