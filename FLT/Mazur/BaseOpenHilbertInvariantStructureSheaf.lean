/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.BaseOpenHilbertOriginalInvariantFunctions

/-!
# The actual invariant quotient sheaf on base-local Hilbert charts

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
  (d : ℕ) (T₀ : Over (Spec (.of R))) [IsOpenImmersion T₀.hom]
  (c : (relativeFppfSheaf f).obj.obj (op T₀))

/-- The actual invariant quotient sheaf, evaluated on base-local parameter opens. -/
def baseOpenChartInvariantPresheaf :
    (variableHilbertTest f d T₀).left.carrier.Presheaf CommRingCat :=
  (baseOpenChartOrbitOpens f hL d T₀ c).op ⋙
    (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj

/-- Pullback of actual invariant functions to the original open source, naturally in the open. -/
def baseOpenChartInvariantToSource : baseOpenChartInvariantPresheaf f hL d T₀ c ⟶
    (Opens.map (variableSourceParameter f hL d T₀ c).left.base).op ⋙
      (variableSourceIntersection f hL d T₀ c).left.presheaf :=
  Functor.whiskerLeft (baseOpenChartOrbitOpens f hL d T₀ c).op
    (invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom ≫
      (baseOpenChartSourcePresheafIso f hL d T₀ c).hom

/-- Every actual invariant-sheaf section is exactly a compatible original source section. -/
def baseOpenChartInvariantRingEquiv (W : (variableHilbertTest f d T₀).left.Opens) :
    (baseOpenChartInvariantPresheaf f hL d T₀ c).obj (op W) ≃+*
      SchemeEffectiveEpiSections.compatibleOpenSections
        (g := (variableSourceParameter f hL d T₀ c).left)
        ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) W :=
  (invariantSectionRingEquivOn (smoothHilbertEquivalenceRelation f hL)
    ((baseOpenChartOrbitOpens f hL d T₀ c).obj W) _
    (baseOpenChartOrbitOpen_preimage f hL d T₀ c W)
    (baseOpenChartSourceImage_invariant f hL d T₀ c W)).trans
      (baseOpenChartOriginalInvariantRingEquiv f hL d T₀ c W)

/-- The ring equivalence retains the actual natural pullback of invariant functions. -/
theorem baseOpenChartInvariantRingEquiv_source
    (W : (variableHilbertTest f d T₀).left.Opens)
    (s : (baseOpenChartInvariantPresheaf f hL d T₀ c).obj (op W)) :
    (baseOpenChartInvariantRingEquiv f hL d T₀ c W s).val =
      (baseOpenChartInvariantToSource f hL d T₀ c).app (op W) s := by
  change ((variableSourceInclusion f hL d T₀ c).left.appIso _).hom
    ((invariantSectionRingEquivOn (smoothHilbertEquivalenceRelation f hL)
      ((baseOpenChartOrbitOpens f hL d T₀ c).obj W) _
      (baseOpenChartOrbitOpen_preimage f hL d T₀ c W)
      (baseOpenChartSourceImage_invariant f hL d T₀ c W) s).val) = _
  rw [invariantSectionRingEquivOn_val]
  change (baseOpenChartSourceSectionsIso f hL d T₀ c W).hom
    ((invariantInclusion (smoothHilbertEquivalenceRelation f hL)).hom.app
      (op ((baseOpenChartOrbitOpens f hL d T₀ c).obj W)) s) = _
  rw [← baseOpenChartSourcePresheafIso_app]
  rfl

/-- Original invariant functions and kernel-pair functions agree naturally on all opens. -/
def baseOpenChartInvariantCompatibleIso : baseOpenChartInvariantPresheaf f hL d T₀ c ≅
    SchemeEffectiveEpiSections.compatibleSectionPresheaf
      (g := (variableSourceParameter f hL d T₀ c).left)
      ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) :=
  NatIso.ofComponents (fun W ↦
    (baseOpenChartInvariantRingEquiv f hL d T₀ c W.unop).toCommRingCatIso) (by
      intro W V k
      ext s
      apply Subtype.ext
      change (baseOpenChartInvariantRingEquiv f hL d T₀ c V.unop
        ((baseOpenChartInvariantPresheaf f hL d T₀ c).map k s)).val =
        (variableSourceIntersection f hL d T₀ c).left.presheaf.map
          ((Opens.map (variableSourceParameter f hL d T₀ c).left.base).map k.unop).op
            (baseOpenChartInvariantRingEquiv f hL d T₀ c W.unop s).val
      rw [baseOpenChartInvariantRingEquiv_source, baseOpenChartInvariantRingEquiv_source]
      exact congrArg (fun m ↦ m s) ((baseOpenChartInvariantToSource f hL d T₀ c).naturality k))

/-- The original invariant quotient sheaf on a base-local chart is its actual structure sheaf. -/
def baseOpenChartInvariantStructureIso :
    baseOpenChartInvariantPresheaf f hL d T₀ c ≅ (variableHilbertTest f d T₀).left.presheaf :=
  baseOpenChartInvariantCompatibleIso f hL d T₀ c ≪≫
    (SchemeEffectiveEpiSections.compatibleSectionPresheafIso
      (g := (variableSourceParameter f hL d T₀ c).left)
      ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _))).symm

/-- The identified invariant-function presheaf is a sheaf on the actual parameter scheme. -/
theorem baseOpenChartInvariantPresheaf_isSheaf :
    (baseOpenChartInvariantPresheaf f hL d T₀ c).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_iso (baseOpenChartInvariantStructureIso f hL d T₀ c).symm
    (variableHilbertTest f d T₀).left.sheaf.property

end FLT.Mazur.HilbertChart
