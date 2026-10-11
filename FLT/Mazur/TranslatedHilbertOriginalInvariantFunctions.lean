/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeKernelPairSectionSheaf
public import FLT.Mazur.SchemeOpenRelationSections
public import FLT.Mazur.TranslatedHilbertRelationOpenSections

/-!
# Original invariant functions on every translated chart open

The section isomorphisms of the actual source and relation open immersions
identify the full original invariant equation with the parameter-cover kernel
pair equation. Effective descent therefore computes original invariants on
every chart open using the actual parameter structure sheaf.
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

/-- The source immersion image of every parameter inverse image remains invariant. -/
theorem translatedChartSourceImage_invariant (W : (acyclicHilbertTest f i.1).left.Opens) :
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
        ((translatedSourceInclusion f hL i).left ''ᵁ
          ((translatedSourceParameter f hL i).left ⁻¹ᵁ W)) =
      (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ
        ((translatedSourceInclusion f hL i).left ''ᵁ
          ((translatedSourceParameter f hL i).left ⁻¹ᵁ W)) := by
  rw [← translatedChartOrbitOpen_preimage]
  exact pullOpen_preimage_eq (smoothHilbertEquivalenceRelation f hL) _

/-- Invariant original functions on the source domain of an actual quotient chart subopen. -/
def translatedChartOriginalInvariants (W : (acyclicHilbertTest f i.1).left.Opens) :
    Subring Γ((smoothHilbertSource f).left,
      (translatedSourceInclusion f hL i).left ''ᵁ
        ((translatedSourceParameter f hL i).left ⁻¹ᵁ W)) :=
  RingHom.eqLocus ((smoothHilbertRelationFst f hL).left.app _).hom
    ((smoothHilbertRelationSnd f hL).left.appLE _ _
      (translatedChartSourceImage_invariant f hL i W).le).hom

/-- The actual open immersions preserve and detect the full original invariance equation. -/
theorem translatedChartOriginalInvariant_iff (W : (acyclicHilbertTest f i.1).left.Opens)
    (s : Γ((smoothHilbertSource f).left,
      (translatedSourceInclusion f hL i).left ''ᵁ
        ((translatedSourceParameter f hL i).left ⁻¹ᵁ W))) :
    ((translatedSourceInclusion f hL i).left.appIso _).hom s ∈
        SchemeEffectiveEpiSections.compatibleOpenSections
          (g := (translatedSourceParameter f hL i).left)
          ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W ↔
      s ∈ translatedChartOriginalInvariants f hL i W :=
  SchemeOpenRelationSections.compatibility_iff
    (translatedSourceInclusion f hL i).left (translatedRestrictedToRelation f hL i).left
    (translatedRestrictedFst f hL i).left (translatedRestrictedSnd f hL i).left
    (smoothHilbertRelationFst f hL).left (smoothHilbertRelationSnd f hL).left
    (congrArg Over.Hom.left (translatedRestrictedToRelation_fst f hL i)).symm
    (congrArg Over.Hom.left (translatedRestrictedToRelation_snd f hL i)).symm
    ((translatedSourceParameter f hL i).left ⁻¹ᵁ W)
    (translatedRestricted_image_fst f hL i _)
    (SchemeEffectiveEpiSections.kernelPair_preimage_open
      ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W).le
    (translatedChartSourceImage_invariant f hL i W).le s

/-- Original invariants and restricted kernel-pair invariants are the same ring. -/
def translatedChartOriginalInvariantRingEquiv (W : (acyclicHilbertTest f i.1).left.Opens) :
    translatedChartOriginalInvariants f hL i W ≃+*
      SchemeEffectiveEpiSections.compatibleOpenSections
        (g := (translatedSourceParameter f hL i).left)
        ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W := by
  let φ := ((translatedSourceInclusion f hL i).left.appIso
    ((translatedSourceParameter f hL i).left ⁻¹ᵁ W)).commRingCatIsoToRingEquiv
  let ψ := (φ.toRingHom.comp (translatedChartOriginalInvariants f hL i W).subtype).codRestrict
    _ (fun s ↦ (translatedChartOriginalInvariant_iff f hL i W s.val).mpr s.property)
  apply RingEquiv.ofBijective ψ
  constructor
  · intro s t h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  · intro s
    have hs : φ.symm s.val ∈ translatedChartOriginalInvariants f hL i W := by
      apply (translatedChartOriginalInvariant_iff f hL i W _).mp
      change φ (φ.symm s.val) ∈ _
      simpa only [RingEquiv.apply_symm_apply] using s.property
    exact ⟨⟨φ.symm s.val, hs⟩, Subtype.ext (φ.apply_symm_apply s.val)⟩

/-- Every chart section ring is identified with the full original invariant-function ring. -/
def translatedChartOriginalFunctionRingEquiv (W : (acyclicHilbertTest f i.1).left.Opens) :
    Γ((acyclicHilbertTest f i.1).left, W) ≃+*
      translatedChartOriginalInvariants f hL i W :=
  (SchemeEffectiveEpiSections.compatibleOpenSectionsEquiv
    (g := (translatedSourceParameter f hL i).left)
    ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W).trans
      (translatedChartOriginalInvariantRingEquiv f hL i W).symm

end FLT.Mazur.HilbertChart
