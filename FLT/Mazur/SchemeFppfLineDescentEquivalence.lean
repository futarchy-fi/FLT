/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfLineRecoveryTriangle

/-!
# Effective categorical fppf descent for line bundles

Canonical pullback and the actual affine-chart gluing construction are inverse
equivalences. Both chosen recoveries are retained, with their proved triangle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemeGeometricDescent SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
/-- Effective descent of actual line bundles along a surjective fppf morphism. -/
def lineDescentEquivalence : LineBundleCat X ≌ LineData p where
  functor := lineCanonical p
  inverse := lineGluing p
  unitIso := lineBaseRecovery p
  counitIso := lineSourceRecovery p
  functor_unitIso_comp := lineBaseRecovery_triangle p

/-- The equivalence uses the prescribed base recovery on every line bundle. -/
lemma lineDescentEquivalence_unit (L : LineBundleCat X) :
    (lineDescentEquivalence p).unitIso.app L = lineBaseRecoveryIso p L := rfl

/-- The equivalence uses the prescribed reconstruction of the original source datum. -/
lemma lineDescentEquivalence_counit (D : LineData p) :
    (lineDescentEquivalence p).counitIso.app D = lineSourceRecoveryIso p D := rfl

/-- Canonical fppf descent is full: every compatible source map descends. -/
instance : (lineCanonical p).Full := (lineDescentEquivalence p).full_functor

/-- Gluing satisfies the other triangle with the same chosen recovery maps. -/
@[reassoc]
lemma lineSourceRecovery_triangle (D : LineData p) :
    (lineBaseRecovery p).hom.app ((lineGluing p).obj D) ≫
        (lineGluing p).map ((lineSourceRecovery p).hom.app D) =
      𝟙 ((lineGluing p).obj D) :=
  (lineDescentEquivalence p).unit_inverse_comp D

end FLT.Mazur.SchemeAffineDescent
