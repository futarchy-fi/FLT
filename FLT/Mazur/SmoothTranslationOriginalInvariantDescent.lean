/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationRestrictedRelationCover
public import FLT.Mazur.SchemeRelationLocalFunctionDescent
public import FLT.Mazur.RelativeRelationInvariantSectionRings

/-!
# Original invariant sections descend through a smooth translation source

On every invariant original-source open contained in the translation image,
the original invariant ring is identified with the full restricted relation's
invariant ring on the common source. The covers used here are proved geometric
covers; the original full source map need not be globally surjective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The source-coordinate kernel pair maps to the original restricted relation. -/
def variableSourceKernelToRestricted :
    pullback (variableSourceInclusion f hL d V c) (variableSourceInclusion f hL d V c) ⟶
      baseOpenRestrictedRelation f hL d V c :=
  (variableRestrictedRelation_lift f hL d V c (pullback.fst _ _) (pullback.snd _ _)
    (by rw [pullback.condition])).choose

@[reassoc]
theorem variableSourceKernelToRestricted_fst :
    variableSourceKernelToRestricted f hL d V c ≫ baseOpenRestrictedFst f hL d V c =
      pullback.fst _ _ :=
  (variableRestrictedRelation_lift f hL d V c _ _ (by rw [pullback.condition])).choose_spec.1.1

@[reassoc]
theorem variableSourceKernelToRestricted_snd :
    variableSourceKernelToRestricted f hL d V c ≫ baseOpenRestrictedSnd f hL d V c =
      pullback.snd _ _ :=
  (variableRestrictedRelation_lift f hL d V c _ _ (by rw [pullback.condition])).choose_spec.1.2

variable (W : (smoothHilbertSource f).left.Opens)
  (hW : (smoothHilbertRelationFst f hL).left ⁻¹ᵁ W =
    (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ W)

include hW in
/-- Every original invariant open pulls back to an invariant common-source open. -/
theorem originalCommonSourceOpen_invariant :
    (baseOpenRestrictedFst f hL d V c).left ⁻¹ᵁ
        ((variableSourceInclusion f hL d V c).left ⁻¹ᵁ W) =
      (baseOpenRestrictedSnd f hL d V c).left ⁻¹ᵁ
        ((variableSourceInclusion f hL d V c).left ⁻¹ᵁ W) :=
  relationSource_preimage (variableSourceInclusion f hL d V c).left
    (baseOpenRestrictedToRelation f hL d V c).left
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_fst f hL d V c))
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_snd f hL d V c)) W hW

variable [Smooth V.hom] (hRange : W ≤ smoothTranslationSourceOpen f hL d V c)

/-- Original invariants on each quotient-neighborhood open are common-source invariants. -/
def smoothTranslationOriginalInvariantRingEquiv :
    relationOpenFunctions (smoothHilbertRelationFst f hL).left
        (smoothHilbertRelationSnd f hL).left W hW ≃+*
      relationOpenFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left
        ((variableSourceInclusion f hL d V c).left ⁻¹ᵁ W)
        (originalCommonSourceOpen_invariant f hL d V c W hW) := by
  let _ := smoothTranslationSourceRestriction_surjective f hL d V c W hRange
  let _ := smoothTranslationRelationRestriction_surjective f hL d V c W hRange
  exact relationLocalInvariantRingEquiv (variableSourceInclusion f hL d V c).left
    (baseOpenRestrictedToRelation f hL d V c).left
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_fst f hL d V c))
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_snd f hL d V c)) W hW
    ((IsPullback.of_hasPullback _ _).map (Over.forget _))
    (variableSourceKernelToRestricted f hL d V c).left
    (congrArg Over.Hom.left (variableSourceKernelToRestricted_fst f hL d V c))
    (congrArg Over.Hom.left (variableSourceKernelToRestricted_snd f hL d V c))

/-- The original invariant comparison retains actual common-source pullback of sections. -/
theorem smoothTranslationOriginalInvariantRingEquiv_val
    (s : relationOpenFunctions (smoothHilbertRelationFst f hL).left
      (smoothHilbertRelationSnd f hL).left W hW) :
    (smoothTranslationOriginalInvariantRingEquiv f hL d V c W hW hRange s).val =
      (variableSourceInclusion f hL d V c).left.app W s.val := by
  let _ := smoothTranslationSourceRestriction_surjective f hL d V c W hRange
  let _ := smoothTranslationRelationRestriction_surjective f hL d V c W hRange
  exact relationLocalInvariantRingEquiv_val _ _
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_fst f hL d V c))
    (congrArg Over.Hom.left (baseOpenRestrictedToRelation_snd f hL d V c)) W hW
    ((IsPullback.of_hasPullback _ _).map (Over.forget _))
    (variableSourceKernelToRestricted f hL d V c).left
    (congrArg Over.Hom.left (variableSourceKernelToRestricted_fst f hL d V c))
    (congrArg Over.Hom.left (variableSourceKernelToRestricted_snd f hL d V c)) s

end FLT.Mazur.HilbertChart
