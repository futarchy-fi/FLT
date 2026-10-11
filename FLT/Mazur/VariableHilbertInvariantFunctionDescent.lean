/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRelationCover
public import FLT.Mazur.SchemeRelationFunctionDescent

/-!
# Full chart invariants descend through the original common source

The full original restricted relation contains the parameter cover's kernel
pair, but need not equal it. Descent through that kernel pair and detection
through the relation cover identify the two actual invariant function rings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Equal parameter maps give an actual restricted relation arrow for arbitrary bases. -/
theorem variableParameterKernel_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ variableSourceIntersection f hL d V c)
    (h : a ≫ variableSourceParameter f hL d V c = b ≫ variableSourceParameter f hL d V c) :
    ∃! k : T ⟶ baseOpenRestrictedRelation f hL d V c,
      k ≫ baseOpenRestrictedFst f hL d V c = a ∧
        k ≫ baseOpenRestrictedSnd f hL d V c = b :=
  variableRestrictedRelation_lift f hL d V c a b (by
    rw [variableSourceClass_eq_parameter, variableSourceClass_eq_parameter, h])

/-- The parameter cover's kernel pair maps to the full restricted relation. -/
def variableParameterKernelToRestricted :
    pullback (variableSourceParameter f hL d V c) (variableSourceParameter f hL d V c) ⟶
      baseOpenRestrictedRelation f hL d V c :=
  (variableParameterKernel_lift f hL d V c (pullback.fst _ _) (pullback.snd _ _)
    pullback.condition).choose

@[reassoc]
theorem variableParameterKernelToRestricted_fst :
    variableParameterKernelToRestricted f hL d V c ≫ baseOpenRestrictedFst f hL d V c =
      pullback.fst _ _ :=
  (variableParameterKernel_lift f hL d V c _ _ pullback.condition).choose_spec.1.1

@[reassoc]
theorem variableParameterKernelToRestricted_snd :
    variableParameterKernelToRestricted f hL d V c ≫ baseOpenRestrictedSnd f hL d V c =
      pullback.snd _ _ :=
  (variableParameterKernel_lift f hL d V c _ _ pullback.condition).choose_spec.1.2

/-- The full chart invariant ring equals the original restricted invariant ring. -/
def variableChartInvariantFunctionRingEquiv :
    compatibleFunctions (variableChartRelationFst f hL d V c).left
        (variableChartRelationSnd f hL d V c).left ≃+*
      compatibleFunctions (baseOpenRestrictedFst f hL d V c).left
        (baseOpenRestrictedSnd f hL d V c).left :=
  relationFunctionRingEquiv (variableSourceParameter f hL d V c).left
    (variableRestrictedToChartRelation f hL d V c).left
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_fst f hL d V c))
    (congrArg Over.Hom.left (variableRestrictedToChartRelation_snd f hL d V c))
    ((IsPullback.of_hasPullback _ _).map (Over.forget _))
    (variableParameterKernelToRestricted f hL d V c).left
    (congrArg Over.Hom.left (variableParameterKernelToRestricted_fst f hL d V c))
    (congrArg Over.Hom.left (variableParameterKernelToRestricted_snd f hL d V c))

/-- The invariant-ring identification is actual pullback along the smooth parameter cover. -/
theorem variableChartInvariantFunctionRingEquiv_val
    (s : compatibleFunctions (variableChartRelationFst f hL d V c).left
      (variableChartRelationSnd f hL d V c).left) :
    (variableChartInvariantFunctionRingEquiv f hL d V c s).val =
      (variableSourceParameter f hL d V c).left.appTop s.val := rfl

end FLT.Mazur.HilbertChart
