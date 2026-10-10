/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyTripleRecovery
public import FLT.Mazur.SchemeFppfFamilyTripleCover
public import FLT.Mazur.SchemeOverlapCocycleDetection
public import FLT.Mazur.SchemeGeometricDescentData

/-!
# The assembled overlap satisfies the original family cocycles

The original unequal triple laws imply the normalized laws on every triple
chart. Joint surjectivity then detects the cocycle on the total overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules) (e : PairIsomorphisms 𝒰 M)

/-- The supplied cocycles use only original modules and original unequal triples. -/
def MemberCocycles : Prop := ∀ ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀,
  SchemeIndependentTripleCocycle.Cocycle (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)
    (M ijk.1.1) (M ijk.1.2) (M ijk.2) (e ijk.1) (e (ijk.1.2, ijk.2))
    (e (ijk.1.1, ijk.2))

/-- Original member cocycles give the assembled cocycle on each original triple chart. -/
lemma tripleEdge_cocycle (he : MemberCocycles 𝒰 M e)
    (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    (tripleEdge12 𝒰 M e ijk).hom ≫ (tripleEdge23 𝒰 M e ijk).hom =
      (tripleEdge13 𝒰 M e ijk).hom :=
  SchemeIndependentTripleCocycle.comp_of_coordinateIso
    (tripleRecovery1 𝒰 M ijk) (tripleRecovery2 𝒰 M ijk) (tripleRecovery3 𝒰 M ijk)
    _ _ _ _ _ _ (tripleEdge12_recovery 𝒰 M e ijk) (tripleEdge23_recovery 𝒰 M e ijk)
    (tripleEdge13_recovery 𝒰 M e ijk) (he ijk)

/-- The actual assembled overlap satisfies its cocycle from the original triple laws. -/
lemma assembledOverlap_cocycle (he : MemberCocycles 𝒰 M e) :
    SchemeGeometricDescent.Cocycle (projection 𝒰)
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e) := by
  apply SchemeOverlapCocycleChart.hom_comp_of_normalized_cover
    (tripleChart 𝒰) (tripleChartMap 𝒰) (tripleChart_jointly_covers 𝒰)
  exact tripleEdge_cocycle 𝒰 M e he

end FLT.Mazur.SchemeFppfFamily
