/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationChartOrbitHomeomorph

/-!
# The identical common-source domains of both invariant sheaves

An original quotient open induces a full-relation invariant parameter open.
The two pullbacks of these opens to the common source agree as actual scheme
opens, giving the domain identification required to compare regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (O : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL)))

/-- The full chart parameter domain over an actual original quotient open. -/
def smoothTranslationParameterOpen : (variableHilbertTest f d V).left.Opens :=
  ⟨{x | (smoothTranslationChartToOrbit f hL d V c x).val ∈ O},
    O.isOpen.preimage (continuous_subtype_val.comp
      (smoothTranslationChartToOrbit f hL d V c).continuous)⟩

/-- The parameter domain is invariant under its actual full equal-class relation. -/
theorem smoothTranslationParameterOpen_invariant :
    (variableChartRelationFst f hL d V c).left ⁻¹ᵁ smoothTranslationParameterOpen f hL d V c O =
      (variableChartRelationSnd f hL d V c).left ⁻¹ᵁ
        smoothTranslationParameterOpen f hL d V c O := by
  ext a
  change (smoothTranslationChartToOrbit f hL d V c
    ((variableChartRelationFst f hL d V c).left a)).val ∈ O ↔
      (smoothTranslationChartToOrbit f hL d V c
        ((variableChartRelationSnd f hL d V c).left a)).val ∈ O
  rw [(smoothTranslationChartToOrbit_eq_iff f hL d V c _ _).mpr ⟨a, rfl, rfl⟩]

/-- Both original and chart invariant functions live on the identical common-source open. -/
theorem smoothTranslationCommonOpen_eq :
    (variableSourceInclusion f hL d V c).left ⁻¹ᵁ
        (pullOpen (smoothHilbertEquivalenceRelation f hL) O).val =
      (variableSourceParameter f hL d V c).left ⁻¹ᵁ
        smoothTranslationParameterOpen f hL d V c O := by
  ext x
  change projection (smoothHilbertEquivalenceRelation f hL)
    ((variableSourceInclusion f hL d V c).left x) ∈ O ↔
      (smoothTranslationChartToOrbit f hL d V c
        ((variableSourceParameter f hL d V c).left x)).val ∈ O
  rw [smoothTranslationChartToOrbit_parameter]
  rfl

/-- An open inside the quotient neighborhood pulls back inside the actual source image. -/
theorem smoothTranslationPullOpen_le
    (hO : O ≤ smoothTranslationOrbitOpen f hL d V c) :
    (pullOpen (smoothHilbertEquivalenceRelation f hL) O).val ≤
      smoothTranslationSourceOpen f hL d V c := by
  intro x hx
  exact (mem_smoothTranslationOrbitOpen_iff f hL d V c x).mp (hO hx)

/-- The corresponding actual open of the full chart orbit quotient. -/
def smoothTranslationFullChartOrbitOpen :
    TopologicalSpace.Opens (Orbit (variableChartEquivalenceRelation f hL d V c)) :=
  descendOpen (variableChartEquivalenceRelation f hL d V c)
    ⟨smoothTranslationParameterOpen f hL d V c O,
      smoothTranslationParameterOpen_invariant f hL d V c O⟩

/-- Its inverse image on the parameter is the previously constructed actual parameter domain. -/
theorem smoothTranslationFullChartOrbitOpen_pull :
    (pullOpen (variableChartEquivalenceRelation f hL d V c)
      (smoothTranslationFullChartOrbitOpen f hL d V c O)).val =
        smoothTranslationParameterOpen f hL d V c O := by
  exact congrArg Subtype.val (pullOpen_descendOpen (variableChartEquivalenceRelation f hL d V c)
    ⟨smoothTranslationParameterOpen f hL d V c O,
      smoothTranslationParameterOpen_invariant f hL d V c O⟩)

end FLT.Mazur.HilbertChart
