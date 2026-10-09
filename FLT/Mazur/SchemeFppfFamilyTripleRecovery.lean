/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairTestRecovery
public import FLT.Mazur.SchemeFppfFamilyTripleRecovery12
public import FLT.Mazur.SchemeFppfFamilyTripleRecovery23

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

/-- Edge 13 retains the original independent pair equation on the triple. -/
lemma tripleEdge13_recovery (e : PairIsomorphisms 𝒰 M)
    (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    (tripleEdge13 𝒰 M e ijk).hom ≫ (tripleRecovery3 𝒰 M ijk).hom =
      (tripleRecovery1 𝒰 M ijk).hom ≫
        (SchemeIndependentTripleCocycle.edge13
          (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)
          (M ijk.1.1) (M ijk.2) (e (ijk.1.1, ijk.2))).hom := by
  dsimp only [tripleEdge13, tripleRecovery1, tripleRecovery3,
    SchemeIndependentTripleCocycle.edge13]
  exact pairTest_normalize_recovery 𝒰 M e (ijk.1.1, ijk.2)
    (SchemeFamilyTripleOverlap.pair13 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (tripleChartMap 𝒰 ijk)
    (SchemeTripleOverlap.pair13 (projection 𝒰))
    (SchemeTripleOverlap.coord1 (projection 𝒰)) (SchemeTripleOverlap.coord3 (projection 𝒰))
    (SchemeTripleOverlap.pair13_fst _) (SchemeTripleOverlap.pair13_snd _)
    (tripleChartMap_pair13 𝒰 ijk)
    (SchemeFamilyTripleOverlap.coord1 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (SchemeFamilyTripleOverlap.coord3 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (SchemeFamilyTripleOverlap.pair13_fst _ _ _) (SchemeFamilyTripleOverlap.pair13_snd _ _ _)
    (tripleChartMap_coord1 𝒰 ijk).symm (tripleChartMap_coord3 𝒰 ijk).symm

end FLT.Mazur.SchemeFppfFamily
