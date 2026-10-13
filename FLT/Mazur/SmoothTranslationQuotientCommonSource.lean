/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationCommonSectionSquare
public import FLT.Mazur.RelativeRelationInvariantMap

/-!
# The full original common-source square of locally ringed spaces

The constructed quotient inclusion commutes with both original common-source
maps, including the actual structure sheaves on every quotient open.
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
local notation "a" => variableSourceInclusion f hL d V c
local notation "j" => smoothTranslationQuotientInclusion f hL d V c

/-- The inclusion commutes with the ORIGINAL common source as locally ringed morphisms. -/
@[reassoc]
theorem smoothTranslationQuotientInclusion_commonSource :
    (p).left.toLRSHom ≫ invariantLocallyRingedProjection e' ≫ j =
      (a).left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  apply LocallyRingedSpace.Hom.ext'
  change ((p).left.toLRSHom.toShHom ≫
    (invariantLocallyRingedProjection e').toShHom ≫ (j).toShHom).hom =
    ((a).left.toLRSHom.toShHom ≫ (invariantLocallyRingedProjection e).toShHom).hom
  rw [invariantLocallyRingedProjection_toShHom, invariantLocallyRingedProjection_toShHom]
  refine PresheafedSpace.Hom.ext _ _ ?_ ?_
  · ext x
    change (j).base (projection e' ((p).left x)) = projection e ((a).left x)
    rw [smoothTranslationQuotientInclusion_projection,
      smoothTranslationChartToOrbit_parameter]
    rfl
  · ext O s
    change (variableSourceIntersection f hL d V c).left.presheaf.map
      (eqToHom (congrArg op (by
        ext x
        change (j).base (projection e' ((p).left x)) ∈ O ↔
          projection e ((a).left x) ∈ O
        rw [smoothTranslationQuotientInclusion_projection,
          smoothTranslationChartToOrbit_parameter]
        rfl)))
      ((p).left.app _ ((invariantInclusion e').hom.app _ ((j).c.app (op O) s))) =
        (a).left.app _ ((invariantInclusion e).hom.app (op O) s)
    rw [smoothTranslationQuotientInclusion_app]
    have hn := (invariantInclusion e').hom.naturality
      (eqToHom (congrArg op (smoothTranslationNeighborhoodChartOpen_eq f hL d V c
        ((TopologicalSpace.Opens.map
          (smoothTranslationNeighborhoodInclusion f hL d V c)).obj O))))
    have hn' := congrArg (fun g ↦ g
      (smoothTranslationInvariantSectionRingEquiv f hL d V c
        (smoothTranslationInclusionDomain f hL d V c O)
        (smoothTranslationNeighborhoodOpen_le f hL d V c _)
        ((invariantSheaf e).obj.map
          (homOfLE (smoothTranslationInclusionDomain_le f hL d V c O)).op s))) hn
    simp only [CommRingCat.comp_apply] at hn'
    erw [hn']
    erw [sectionPullback_transport (p).left
      (congrArg (fun Z ↦ (pullOpen e' Z).val)
        (smoothTranslationNeighborhoodChartOpen_eq f hL d V c
          ((TopologicalSpace.Opens.map
            (smoothTranslationNeighborhoodInclusion f hL d V c)).obj O)))]
    let D := smoothTranslationInclusionDomain f hL d V c O
    let s' := (invariantSheaf e).obj.map
      (homOfLE (smoothTranslationInclusionDomain_le f hL d V c O)).op s
    let hD := smoothTranslationNeighborhoodOpen_le f hL d V c
      ((TopologicalSpace.Opens.map (smoothTranslationNeighborhoodInclusion f hL d V c)).obj O)
    have hU := smoothTranslationInclusion_commonOpen f hL d V c O
    have hc := smoothTranslationChartSectionEquiv_val f hL d V c D
      (smoothTranslationInvariantSectionRingEquiv f hL d V c D hD s')
    rw [sectionPullback_transport _
      (smoothTranslationFullChartOrbitOpen_pull f hL d V c D)] at hc
    calc
      _ = (variableSourceIntersection f hL d V c).left.presheaf.map
          (eqToHom (congrArg op hU))
          (smoothTranslationChartSectionEquiv f hL d V c D
            (smoothTranslationInvariantSectionRingEquiv f hL d V c D hD s')).val := by
        rw [hc]
        erw [sectionMaps_comp, sectionMaps_comp]
        rfl
      _ = _ := smoothTranslationInclusion_commonSection f hL d V c O s

end FLT.Mazur.HilbertChart
