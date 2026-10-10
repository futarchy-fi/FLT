/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeLineBundleCategory
public import FLT.Mazur.SchemeLineDescentCategory
public import FLT.Mazur.SchemeFppfSourceLineMapEquivalence

/-!
# The fully faithful fppf line-bundle gluing functor

Effective gluing of objects and compatible maps defines a functor. Its actual
map preimage and the proved map round trips establish full faithfulness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- Effective fppf gluing of geometric line-bundle descent data and compatible maps. -/
def lineGluing : LineData p ⥤ LineBundleCat X where
  obj D := ⟨fppfSourceLineGlued p D.datum D.rankOne,
    fppfSourceLineGlued_locallyFreeRankOne p D.datum D.rankOne⟩
  map {D E} f := InducedCategory.homMk
    (fppfSourceLineMap p D.datum E.datum D.rankOne E.rankOne f.val f.property)
  map_id D := InducedCategory.hom_ext
    (fppfSourceLineMap_identity p D.datum D.rankOne D.datum.mapCompatible_id)
  map_comp {D E F} f g := InducedCategory.hom_ext
    (fppfSourceLineMap_composition p D.datum E.datum F.datum D.rankOne E.rankOne F.rankOne
      f.val g.val f.property g.property _)

/-- Every map of glued line bundles has its unique compatible source preimage. -/
def lineGluingFullyFaithful : (lineGluing p).FullyFaithful where
  preimage {D E} f := (fppfSourceLineMapEquiv p D.datum E.datum D.rankOne E.rankOne).symm f.hom
  map_preimage {D E} f := InducedCategory.hom_ext
    ((fppfSourceLineMapEquiv p D.datum E.datum D.rankOne E.rankOne).apply_symm_apply f.hom)
  preimage_map {D E} f :=
    (fppfSourceLineMapEquiv p D.datum E.datum D.rankOne E.rankOne).symm_apply_apply f

instance : (lineGluing p).Faithful := (lineGluingFullyFaithful p).faithful

instance : (lineGluing p).Full := (lineGluingFullyFaithful p).full

end FLT.Mazur.SchemeAffineDescent
