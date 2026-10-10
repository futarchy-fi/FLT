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

/-- Edge 12 retains the original independent pair equation on the triple. -/
lemma tripleEdge12_recovery (e : PairIsomorphisms 𝒰 M)
    (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    (tripleEdge12 𝒰 M e ijk).hom ≫ (tripleRecovery2 𝒰 M ijk).hom =
      (tripleRecovery1 𝒰 M ijk).hom ≫
        (SchemeIndependentTripleCocycle.edge12
          (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)
          (M ijk.1.1) (M ijk.1.2) (e ijk.1)).hom := by
  dsimp only [tripleEdge12, tripleRecovery1, tripleRecovery2,
    SchemeIndependentTripleCocycle.edge12]
  exact pairTest_normalize_recovery 𝒰 M e ijk.1
    (SchemeFamilyTripleOverlap.pair12 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (tripleChartMap 𝒰 ijk)
    (SchemeTripleOverlap.pair12 (projection 𝒰))
    (SchemeTripleOverlap.coord1 (projection 𝒰)) (SchemeTripleOverlap.coord2 (projection 𝒰))
    rfl rfl
    (tripleChartMap_pair12 𝒰 ijk)
    (SchemeFamilyTripleOverlap.coord1 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (SchemeFamilyTripleOverlap.coord2 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    rfl rfl
    (tripleChartMap_coord1 𝒰 ijk).symm (tripleChartMap_coord2 𝒰 ijk).symm


end FLT.Mazur.SchemeFppfFamily
