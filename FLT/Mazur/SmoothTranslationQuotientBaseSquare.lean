/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationQuotientCommonSource
public import FLT.Mazur.RelativeRelationInvariantMap

/-!
# The original coefficient square for the full translation quotient

The regular-function common-source square and faithful flatness prove equality
of actual locally ringed base maps, not just of their underlying point maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))


local notation "e" => smoothHilbertEquivalenceRelation f hL
local notation "e'" => variableChartEquivalenceRelation f hL d V c
local notation "p" => variableSourceParameter f hL d V c

/-- The full translation quotient inclusion respects the ORIGINAL coefficient base. -/
@[reassoc]
theorem smoothTranslationQuotientInclusion_baseMap :
    smoothTranslationQuotientInclusion f hL d V c ≫ invariantLocallyRingedBaseMap e =
      invariantLocallyRingedBaseMap e' := by
  apply invariantMap_hom_ext e'
  obtain ⟨u, hu⟩ := Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_surjective
    (X := (variableHilbertTest f d V).left) (Y := Spec (.of R))
    (invariantLocallyRingedProjection e' ≫
      smoothTranslationQuotientInclusion f hL d V c ≫ invariantLocallyRingedBaseMap e)
  obtain ⟨v, hv⟩ := Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_surjective
    (X := (variableHilbertTest f d V).left) (Y := Spec (.of R))
    (invariantLocallyRingedProjection e' ≫ invariantLocallyRingedBaseMap e')
  rw [← hu, ← hv]
  apply congrArg Scheme.forgetToLocallyRingedSpace.map
  let _ : Epi (p).left := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (p).left).mp
  apply Scheme.forgetToLocallyRingedSpace.map_injective
  change (p).left.toLRSHom ≫ u.toLRSHom = (p).left.toLRSHom ≫ v.toLRSHom
  change u.toLRSHom = _ at hu
  change v.toLRSHom = _ at hv
  rw [hu, hv, smoothTranslationQuotientInclusion_commonSource_assoc,
    invariantLocallyRingedProjection_baseMap, invariantLocallyRingedProjection_baseMap,
    ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom,
    (variableSourceInclusion f hL d V c).w, (p).w]

end FLT.Mazur.HilbertChart
