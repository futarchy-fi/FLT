/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePicardClasses
public import FLT.Mazur.ModuleLineBundlePullback
public import Mathlib.CategoryTheory.InducedCategory

/-!
# The category of actual line bundles on a scheme

Objects are locally free rank-one module sheaves. Morphisms are all sheaf maps;
the category keeps the existing Picard representatives as its underlying objects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePicard

/-- The category whose objects are actual line bundles and whose maps are sheaf maps. -/
abbrev LineBundleCat (X : Scheme.{u}) :=
  InducedCategory X.Modules (fun M : LineBundle X ↦ M.val)

/-- Forget the rank-one property and retain the actual module sheaf. -/
abbrev lineBundleForget (X : Scheme.{u}) : LineBundleCat X ⥤ X.Modules :=
  inducedFunctor (fun M : LineBundle X ↦ M.val)

/-- Scheme pullback preserves the category of actual line bundles. -/
def lineBundlePullback {X Y : Scheme.{u}} (p : Y ⟶ X) :
    LineBundleCat X ⥤ LineBundleCat Y where
  obj A := ⟨(pullback p).obj A.val, A.property.pullback p⟩
  map f := InducedCategory.homMk ((pullback p).map f.hom)
  map_id A := InducedCategory.hom_ext ((pullback p).map_id A.val)
  map_comp f g := InducedCategory.hom_ext ((pullback p).map_comp f.hom g.hom)

end FLT.Mazur.SchemePicard
