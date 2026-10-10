/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairNormalization
public import FLT.Mazur.SchemeFppfFamilyTripleChart
public import FLT.Mazur.SchemeIndependentTripleCocycle

/-!
# Coordinates and edges on original triple charts

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
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules)

/-- Recover original coordinate 1 on the actual triple chart. -/
def tripleRecovery1 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  recovery (SchemeFamilyTripleOverlap.coord1 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (Limits.Sigma.ι 𝒰.X ijk.1.1)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord1 (projection 𝒰))
    (tripleChartMap_coord1 𝒰 ijk).symm (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (SchemeCoproductModuleGluing.recovery 𝒰.X M ijk.1.1)

/-- Recover original coordinate 2 on the actual triple chart. -/
def tripleRecovery2 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  recovery (SchemeFamilyTripleOverlap.coord2 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (Limits.Sigma.ι 𝒰.X ijk.1.2)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord2 (projection 𝒰))
    (tripleChartMap_coord2 𝒰 ijk).symm (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (SchemeCoproductModuleGluing.recovery 𝒰.X M ijk.1.2)

/-- Recover original coordinate 3 on the actual triple chart. -/
def tripleRecovery3 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  recovery (SchemeFamilyTripleOverlap.coord3 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2))
    (Limits.Sigma.ι 𝒰.X ijk.2)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord3 (projection 𝒰))
    (tripleChartMap_coord3 𝒰 ijk).symm (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (SchemeCoproductModuleGluing.recovery 𝒰.X M ijk.2)

/-- The total edge 12, normalized after pullback to an original triple chart. -/
def tripleEdge12 (e : PairIsomorphisms 𝒰 M) (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  normalize (SchemeTripleOverlap.coord1 (projection 𝒰))
    (SchemeTripleOverlap.coord2 (projection 𝒰)) (tripleChartMap 𝒰 ijk)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord1 (projection 𝒰))
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord2 (projection 𝒰)) rfl rfl
    (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
      (Limits.pullback.snd (projection 𝒰) (projection 𝒰))
      (SchemeTripleOverlap.pair12 (projection 𝒰))
      (SchemeTripleOverlap.coord1 (projection 𝒰)) (SchemeTripleOverlap.coord2 (projection 𝒰))
      rfl rfl
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e))

/-- The total edge 23, normalized after pullback to an original triple chart. -/
def tripleEdge23 (e : PairIsomorphisms 𝒰 M) (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  normalize (SchemeTripleOverlap.coord2 (projection 𝒰))
    (SchemeTripleOverlap.coord3 (projection 𝒰)) (tripleChartMap 𝒰 ijk)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord2 (projection 𝒰))
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord3 (projection 𝒰)) rfl rfl
    (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
      (Limits.pullback.snd (projection 𝒰) (projection 𝒰))
      (SchemeTripleOverlap.pair23 (projection 𝒰))
      (SchemeTripleOverlap.coord2 (projection 𝒰)) (SchemeTripleOverlap.coord3 (projection 𝒰))
      (SchemeTripleOverlap.pair23_fst (projection 𝒰)) rfl
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e))

/-- The total edge 13, normalized after pullback to an original triple chart. -/
def tripleEdge13 (e : PairIsomorphisms 𝒰 M) (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :=
  normalize (SchemeTripleOverlap.coord1 (projection 𝒰))
    (SchemeTripleOverlap.coord3 (projection 𝒰)) (tripleChartMap 𝒰 ijk)
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord1 (projection 𝒰))
    (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord3 (projection 𝒰)) rfl rfl
    (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
      (Limits.pullback.snd (projection 𝒰) (projection 𝒰))
      (SchemeTripleOverlap.pair13 (projection 𝒰))
      (SchemeTripleOverlap.coord1 (projection 𝒰)) (SchemeTripleOverlap.coord3 (projection 𝒰))
      (SchemeTripleOverlap.pair13_fst (projection 𝒰))
      (SchemeTripleOverlap.pair13_snd (projection 𝒰))
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e))

end FLT.Mazur.SchemeFppfFamily
