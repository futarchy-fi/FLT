/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertInvariantFunctionDescent
public import FLT.Mazur.SchemeRelationOpenInvariantRings
public import FLT.Mazur.VariableHilbertChartRelationOperations
public import FLT.Mazur.RelativeRelationInvariantSectionRings

/-!
# The full chart invariant sheaf in common-source coordinates

For every orbit open of the full chart relation, its actual invariant sheaf
sections are the invariant regular functions on the original common source.
The comparison is the actual structure-sheaf pullback along the smooth cover.
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
  (W : (variableHilbertTest f d V).left.Opens)
  (hW : (variableChartRelationFst f hL d V c).left ⁻¹ᵁ W =
    (variableChartRelationSnd f hL d V c).left ⁻¹ᵁ W)

include hW in
/-- Every invariant parameter open gives an invariant common-source open. -/
theorem variableCommonSourceOpen_invariant :
    (baseOpenRestrictedFst f hL d V c).left ⁻¹ᵁ
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ W) =
      (baseOpenRestrictedSnd f hL d V c).left ⁻¹ᵁ
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ W) :=
  relationSource_preimage (variableSourceParameter f hL d V c).left
    (variableRestrictedToChartRelation f hL d V c).left
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_fst f hL d V c))
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_snd f hL d V c)) W hW

/-- Invariants on every full-chart open agree with original common-source invariants. -/
def variableChartOpenInvariantRingEquiv :
    relationOpenFunctions (variableChartRelationFst f hL d V c).left
        (variableChartRelationSnd f hL d V c).left W hW ≃+*
      relationOpenFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ W)
        (variableCommonSourceOpen_invariant f hL d V c W hW) :=
  relationOpenInvariantRingEquiv _ _ W hW (variableSourceParameter f hL d V c).left
    (variableRestrictedToChartRelation f hL d V c).left
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_fst f hL d V c))
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_snd f hL d V c))
    ((IsPullback.of_hasPullback _ _).map (Over.forget _))
    (variableParameterKernelToRestricted f hL d V c).left
    (congrArg Over.Hom.left (variableParameterKernelToRestricted_fst f hL d V c))
    (congrArg Over.Hom.left (variableParameterKernelToRestricted_snd f hL d V c))

/-- The comparison retains the original structure-sheaf pullback. -/
theorem variableChartOpenInvariantRingEquiv_val
    (s : relationOpenFunctions (variableChartRelationFst f hL d V c).left
      (variableChartRelationSnd f hL d V c).left W hW) :
    (variableChartOpenInvariantRingEquiv f hL d V c W hW s).val =
      (variableSourceParameter f hL d V c).left.app W s.val :=
  relationOpenInvariantRingEquiv_val _ _ _ _ _ _ _ _ _ _ _ _ s

variable (O : TopologicalSpace.Opens (Orbit (variableChartEquivalenceRelation f hL d V c)))

/-- Sections of the actual chart invariant sheaf are full common-source invariant functions. -/
def variableChartInvariantSheafSectionEquiv :
    (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj (op O) ≃+*
      relationOpenFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left
        ((variableSourceParameter f hL d V c).left ⁻¹ᵁ
          (pullOpen (variableChartEquivalenceRelation f hL d V c) O).val)
        (variableCommonSourceOpen_invariant f hL d V c _
          (pullOpen_preimage_eq (variableChartEquivalenceRelation f hL d V c) O)) :=
  (invariantSectionRingEquiv (variableChartEquivalenceRelation f hL d V c) O).trans
    (variableChartOpenInvariantRingEquiv f hL d V c _
      (pullOpen_preimage_eq (variableChartEquivalenceRelation f hL d V c) O))

end FLT.Mazur.HilbertChart
