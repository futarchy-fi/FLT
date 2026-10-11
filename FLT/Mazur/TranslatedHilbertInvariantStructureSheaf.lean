/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.TranslatedHilbertOriginalInvariantFunctions

/-!
# The actual invariant quotient sheaf on translated Hilbert charts

Every chart-open section of the original quotient invariant sheaf is identified
with the actual parameter structure sheaf. Both source and relation domains
are the original open subschemes; the ring identifications respect every
restriction map. The locally ringed chart isomorphism is a further packaging step.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The actual invariant quotient sheaf, evaluated on translated parameter opens. -/
def translatedChartInvariantPresheaf :
    (acyclicHilbertTest f i.1).left.carrier.Presheaf CommRingCat :=
  (translatedChartOrbitOpens f hL i).op ⋙
    (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj

/-- Pullback of actual invariant functions to the original open source, naturally in the open. -/
def translatedChartInvariantToSource : translatedChartInvariantPresheaf f hL i ⟶
    (Opens.map (translatedSourceParameter f hL i).left.base).op ⋙
      (translatedSourceIntersection f hL i).left.presheaf :=
  Functor.whiskerLeft (translatedChartOrbitOpens f hL i).op
    (invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom ≫
      (translatedChartSourcePresheafIso f hL i).hom

/-- Every actual invariant-sheaf section is exactly a compatible original source section. -/
def translatedChartInvariantRingEquiv (W : (acyclicHilbertTest f i.1).left.Opens) :
    (translatedChartInvariantPresheaf f hL i).obj (op W) ≃+*
      SchemeEffectiveEpiSections.compatibleOpenSections
        (g := (translatedSourceParameter f hL i).left)
        ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W :=
  (invariantSectionRingEquivOn (smoothHilbertEquivalenceRelation f hL)
    ((translatedChartOrbitOpens f hL i).obj W) _
    (translatedChartOrbitOpen_preimage f hL i W)
    (translatedChartSourceImage_invariant f hL i W)).trans
      (translatedChartOriginalInvariantRingEquiv f hL i W)

/-- The ring equivalence retains the actual natural pullback of invariant functions. -/
theorem translatedChartInvariantRingEquiv_source
    (W : (acyclicHilbertTest f i.1).left.Opens)
    (s : (translatedChartInvariantPresheaf f hL i).obj (op W)) :
    (translatedChartInvariantRingEquiv f hL i W s).val =
      (translatedChartInvariantToSource f hL i).app (op W) s := by
  change ((translatedSourceInclusion f hL i).left.appIso _).hom
    ((invariantSectionRingEquivOn (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W) _
      (translatedChartOrbitOpen_preimage f hL i W)
      (translatedChartSourceImage_invariant f hL i W) s).val) = _
  rw [invariantSectionRingEquivOn_val]
  change (translatedChartSourceSectionsIso f hL i W).hom
    ((invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom.app
      (op ((translatedChartOrbitOpens f hL i).obj W)) s) = _
  rw [← translatedChartSourcePresheafIso_app]
  rfl

/-- Original invariant functions and kernel-pair functions agree naturally on all opens. -/
def translatedChartInvariantCompatibleIso : translatedChartInvariantPresheaf f hL i ≅
    SchemeEffectiveEpiSections.compatibleSectionPresheaf
      (g := (translatedSourceParameter f hL i).left)
      ((translatedRestricted_isPullback f hL i).map (Over.forget _)) :=
  NatIso.ofComponents (fun W ↦
    (translatedChartInvariantRingEquiv f hL i W.unop).toCommRingCatIso) (by
      intro W V k
      ext s
      apply Subtype.ext
      change (translatedChartInvariantRingEquiv f hL i V.unop
        ((translatedChartInvariantPresheaf f hL i).map k s)).val =
        (translatedSourceIntersection f hL i).left.presheaf.map
          ((Opens.map (translatedSourceParameter f hL i).left.base).map k.unop).op
            (translatedChartInvariantRingEquiv f hL i W.unop s).val
      rw [translatedChartInvariantRingEquiv_source, translatedChartInvariantRingEquiv_source]
      exact congrArg (fun m ↦ m s) ((translatedChartInvariantToSource f hL i).naturality k))

/-- The original invariant quotient sheaf on a translated chart is its actual structure sheaf. -/
def translatedChartInvariantStructureIso :
    translatedChartInvariantPresheaf f hL i ≅ (acyclicHilbertTest f i.1).left.presheaf :=
  translatedChartInvariantCompatibleIso f hL i ≪≫
    (SchemeEffectiveEpiSections.compatibleSectionPresheafIso
      (g := (translatedSourceParameter f hL i).left)
      ((translatedRestricted_isPullback f hL i).map (Over.forget _))).symm

/-- The identified invariant-function presheaf is a sheaf on the actual parameter scheme. -/
theorem translatedChartInvariantPresheaf_isSheaf :
    (translatedChartInvariantPresheaf f hL i).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_iso (translatedChartInvariantStructureIso f hL i).symm
    (acyclicHilbertTest f i.1).left.sheaf.property

end FLT.Mazur.HilbertChart
