/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairTestRecovery
public import FLT.Mazur.SchemeFppfFamilyTripleCoordinates

/-!
# The three assembled edges recover the original triple edges

Each normalized edge is compared using the same coordinate recoveries.
In particular, the middle recovery is shared by the two adjacent pairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SheafPullbackCoordinateRecovery SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
attribute [local irreducible] assembledOverlap tripleChartMap pairMap projection
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules)

/-- Edge 23 retains the original independent pair equation on the triple. -/
lemma tripleEdge23_recovery (e : PairIsomorphisms 𝒰 M)
    (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    (tripleEdge23 𝒰 M e ijk).hom ≫ (tripleRecovery3 𝒰 M ijk).hom =
      (tripleRecovery2 𝒰 M ijk).hom ≫
        (SchemeIndependentTripleCocycle.edge23
          (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)
          (M ijk.1.2) (M ijk.2) (e (ijk.1.2, ijk.2))).hom := by
  dsimp only [tripleEdge23, tripleRecovery2, tripleRecovery3,
    SchemeIndependentTripleCocycle.edge23]
  exact pairTest_normalize_recovery 𝒰 M e (ijk.1.2, ijk.2)
    (SchemeFamilyTripleOverlap.pair23 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (tripleChartMap 𝒰 ijk)
    (SchemeTripleOverlap.pair23 (projection 𝒰))
    (SchemeTripleOverlap.coord2 (projection 𝒰)) (SchemeTripleOverlap.coord3 (projection 𝒰))
    (SchemeTripleOverlap.pair23_fst _) rfl
    (tripleChartMap_pair23 𝒰 ijk)
    (SchemeFamilyTripleOverlap.coord2 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (SchemeFamilyTripleOverlap.coord3 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (SchemeFamilyTripleOverlap.pair23_fst _ _ _) rfl
    (tripleChartMap_coord2 𝒰 ijk).symm (tripleChartMap_coord3 𝒰 ijk).symm


end FLT.Mazur.SchemeFppfFamily
