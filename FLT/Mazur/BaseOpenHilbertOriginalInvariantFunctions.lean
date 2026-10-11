/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeKernelPairSectionSheaf
public import FLT.Mazur.SchemeOpenRelationSections
public import FLT.Mazur.BaseOpenHilbertRelationOpenSections

/-!
# Original invariant functions on every base-local chart open

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
  (d : ℕ) (T₀ : Over (Spec (.of R))) [IsOpenImmersion T₀.hom]
  (c : (relativeFppfSheaf f).obj.obj (op T₀))

/-- The source immersion image of every parameter inverse image remains invariant. -/
theorem baseOpenChartSourceImage_invariant (W : (variableHilbertTest f d T₀).left.Opens) :
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ
        ((variableSourceInclusion f hL d T₀ c).left ''ᵁ
          ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W)) =
      (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ
        ((variableSourceInclusion f hL d T₀ c).left ''ᵁ
          ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W)) := by
  rw [← baseOpenChartOrbitOpen_preimage]
  exact pullOpen_preimage_eq (smoothHilbertEquivalenceRelation f hL) _

/-- Invariant original functions on the source domain of an actual quotient chart subopen. -/
def baseOpenChartOriginalInvariants (W : (variableHilbertTest f d T₀).left.Opens) :
    Subring Γ((smoothHilbertSource f).left,
      (variableSourceInclusion f hL d T₀ c).left ''ᵁ
        ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W)) :=
  RingHom.eqLocus ((smoothHilbertRelationFst f hL).left.app _).hom
    ((smoothHilbertRelationSnd f hL).left.appLE _ _
      (baseOpenChartSourceImage_invariant f hL d T₀ c W).le).hom

/-- The actual open immersions preserve and detect the full original invariance equation. -/
theorem baseOpenChartOriginalInvariant_iff (W : (variableHilbertTest f d T₀).left.Opens)
    (s : Γ((smoothHilbertSource f).left,
      (variableSourceInclusion f hL d T₀ c).left ''ᵁ
        ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W))) :
    ((variableSourceInclusion f hL d T₀ c).left.appIso _).hom s ∈
        SchemeEffectiveEpiSections.compatibleOpenSections
          (g := (variableSourceParameter f hL d T₀ c).left)
          ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) W ↔
      s ∈ baseOpenChartOriginalInvariants f hL d T₀ c W :=
  SchemeOpenRelationSections.compatibility_iff
    (variableSourceInclusion f hL d T₀ c).left (baseOpenRestrictedToRelation f hL d T₀ c).left
    (baseOpenRestrictedFst f hL d T₀ c).left (baseOpenRestrictedSnd f hL d T₀ c).left
    (smoothHilbertRelationFst f hL).left (smoothHilbertRelationSnd f hL).left
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_fst f hL d T₀ c)).symm
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_snd f hL d T₀ c)).symm
    ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W)
    (baseOpenRestricted_image_fst f hL d T₀ c _)
    (SchemeEffectiveEpiSections.kernelPair_preimage_open
      ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) W).le
    (baseOpenChartSourceImage_invariant f hL d T₀ c W).le s

/-- Original invariants and restricted kernel-pair invariants are the same ring. -/
def baseOpenChartOriginalInvariantRingEquiv (W : (variableHilbertTest f d T₀).left.Opens) :
    baseOpenChartOriginalInvariants f hL d T₀ c W ≃+*
      SchemeEffectiveEpiSections.compatibleOpenSections
        (g := (variableSourceParameter f hL d T₀ c).left)
        ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) W := by
  let φ := ((variableSourceInclusion f hL d T₀ c).left.appIso
    ((variableSourceParameter f hL d T₀ c).left ⁻¹ᵁ W)).commRingCatIsoToRingEquiv
  let ψ := (φ.toRingHom.comp (baseOpenChartOriginalInvariants f hL d T₀ c W).subtype).codRestrict
    _ (fun s ↦ (baseOpenChartOriginalInvariant_iff f hL d T₀ c W s.val).mpr s.property)
  apply RingEquiv.ofBijective ψ
  constructor
  · intro s t h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  · intro s
    have hs : φ.symm s.val ∈ baseOpenChartOriginalInvariants f hL d T₀ c W := by
      apply (baseOpenChartOriginalInvariant_iff f hL d T₀ c W _).mp
      change φ (φ.symm s.val) ∈ _
      simpa only [RingEquiv.apply_symm_apply] using s.property
    exact ⟨⟨φ.symm s.val, hs⟩, Subtype.ext (φ.apply_symm_apply s.val)⟩

/-- Every chart section ring is identified with the full original invariant-function ring. -/
def baseOpenChartOriginalFunctionRingEquiv (W : (variableHilbertTest f d T₀).left.Opens) :
    Γ((variableHilbertTest f d T₀).left, W) ≃+*
      baseOpenChartOriginalInvariants f hL d T₀ c W :=
  (SchemeEffectiveEpiSections.compatibleOpenSectionsEquiv
    (g := (variableSourceParameter f hL d T₀ c).left)
    ((baseOpenRestricted_isPullback f hL d T₀ c).map (Over.forget _)) W).trans
      (baseOpenChartOriginalInvariantRingEquiv f hL d T₀ c W).symm

end FLT.Mazur.HilbertChart
