/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationInvariantSectionComparison
public import FLT.Mazur.SmoothTranslationInvariantOpenFunctor
public import FLT.Mazur.SchemeSectionTransportNaturality

/-!
# Restriction of the two common-source section coordinates

The actual original and chart section comparisons commute with restriction to
smaller quotient opens, including all structure-sheaf domain transports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {O P : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL))}

/-- Common-source domains preserve inclusions of original quotient opens. -/
theorem smoothTranslationCommonOpen_mono (h : O ≤ P) :
    (variableSourceParameter f hL d V c).left ⁻¹ᵁ
        smoothTranslationParameterOpen f hL d V c O ≤
      (variableSourceParameter f hL d V c).left ⁻¹ᵁ
        smoothTranslationParameterOpen f hL d V c P := fun _ hx ↦ h hx

/-- Original invariant sections restrict in their actual common-source coordinates. -/
theorem smoothTranslationOriginalSectionEquiv_restrict (h : O ≤ P)
    (hP : P ≤ smoothTranslationOrbitOpen f hL d V c)
    (s : (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op P)) :
    (smoothTranslationOriginalSectionEquiv f hL d V c O (h.trans hP)
      ((invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.map
        (homOfLE h).op s)).val =
      (variableSourceIntersection f hL d V c).left.presheaf.map
        (homOfLE (smoothTranslationCommonOpen_mono f hL d V c h)).op
        (smoothTranslationOriginalSectionEquiv f hL d V c P hP s).val := by
  rw [smoothTranslationOriginalSectionEquiv_val, smoothTranslationOriginalSectionEquiv_val]
  rw [sectionTransformation_naturality]
  have hp := sectionPullback_naturality (variableSourceInclusion f hL d V c).left
    (show (pullOpen (smoothHilbertEquivalenceRelation f hL) O).val ≤
      (pullOpen (smoothHilbertEquivalenceRelation f hL) P).val from fun _ hx ↦ h hx)
    ((invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom.app (op P) s)
  exact (congrArg
    ((variableSourceIntersection f hL d V c).left.presheaf.map
      (eqToHom (congrArg op (smoothTranslationCommonOpen_eq f hL d V c O)))) hp).trans
    (sectionTransport_naturality _
      (smoothTranslationCommonOpen_eq f hL d V c P)
      (smoothTranslationCommonOpen_eq f hL d V c O) _ _ _)

/-- Chart invariant sections restrict in exactly the same common-source coordinates. -/
theorem smoothTranslationChartSectionEquiv_restrict (h : O ≤ P)
    (s : (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj
      (op (smoothTranslationFullChartOrbitOpen f hL d V c P))) :
    (smoothTranslationChartSectionEquiv f hL d V c O
      ((invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.map
        (homOfLE (smoothTranslationFullChartOrbitOpen_mono f hL d V c h)).op s)).val =
      (variableSourceIntersection f hL d V c).left.presheaf.map
        (homOfLE (smoothTranslationCommonOpen_mono f hL d V c h)).op
        (smoothTranslationChartSectionEquiv f hL d V c P s).val := by
  rw [smoothTranslationChartSectionEquiv_val, smoothTranslationChartSectionEquiv_val]
  rw [sectionTransformation_naturality]
  have ht := sectionTransport_naturality (variableHilbertTest f d V).left.presheaf
    (smoothTranslationFullChartOrbitOpen_pull f hL d V c P)
    (smoothTranslationFullChartOrbitOpen_pull f hL d V c O)
    (fun _ hx ↦ smoothTranslationFullChartOrbitOpen_mono f hL d V c h hx)
    (smoothTranslationParameterOpen_mono f hL d V c h)
    ((invariantInclusion (variableChartEquivalenceRelation f hL d V c)).hom.app
      (op (smoothTranslationFullChartOrbitOpen f hL d V c P)) s)
  exact (congrArg ((variableSourceParameter f hL d V c).left.app _) ht).trans
    (sectionPullback_naturality _ (smoothTranslationParameterOpen_mono f hL d V c h) _)

end FLT.Mazur.HilbertChart
