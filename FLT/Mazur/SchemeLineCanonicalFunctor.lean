/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeLineBundleCategory
public import FLT.Mazur.SchemeLineDescentCategory
public import FLT.Mazur.SchemeCanonicalDescentData

/-!
# The canonical line-bundle descent functor

Pullback equips every line bundle with its proved canonical geometric descent
datum, and sends each sheaf morphism to its compatible pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Pullback of line bundles with their canonical geometric descent data. -/
def lineCanonical : LineBundleCat X ⥤ LineData p where
  obj A := ⟨(pullback p).obj A.val, A.property.pullback p, canonical p A.val⟩
  map f := ⟨(pullback p).map f.hom, canonical_mapCompatible p f.hom⟩
  map_id A := Subtype.ext ((pullback p).map_id A.val)
  map_comp f g := Subtype.ext ((pullback p).map_comp f.hom g.hom)

end FLT.Mazur.SchemeGeometricDescent
