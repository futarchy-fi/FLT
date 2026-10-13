/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertEtaleRelation

/-!
# Finite presentation and smoothness of full translated Hilbert relations

The full relation is open in the product of the test and translation base.
Both endpoints therefore inherit finite presentation or smoothness from the
translation base, without requiring that base to be etale.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

instance variableHilbertOverlapToTest_locallyOfFinitePresentation
    [LocallyOfFinitePresentation V.hom] :
    LocallyOfFinitePresentation (variableHilbertOverlapToTest f d V c U s).left := by
  let _ : LocallyOfFinitePresentation (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change LocallyOfFinitePresentation ((variableHilbertOverlapArrow f d V c U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

variable {L : X.Modules} (hL : AmpleLineBundle L)

instance variableChartRelationSnd_locallyOfFinitePresentation
    [LocallyOfFinitePresentation V.hom] :
    LocallyOfFinitePresentation (variableChartRelationSnd f hL d V c).left :=
  variableHilbertOverlapToTest_locallyOfFinitePresentation f d V c _ _

instance variableChartRelationFst_locallyOfFinitePresentation
    [LocallyOfFinitePresentation V.hom] :
    LocallyOfFinitePresentation (variableChartRelationFst f hL d V c).left := by
  let e := (Over.forget _).mapIso (variableChartRelationSwapIso f hL d V c)
  have h : e.hom ≫ (variableChartRelationSnd f hL d V c).left =
      (variableChartRelationFst f hL d V c).left :=
    congrArg Over.Hom.left (variableChartEquivalenceRelation f hL d V c).symmetry₂
  rw [← h]
  infer_instance

instance variableChartRelationFst_smooth [Smooth V.hom] :
    Smooth (variableChartRelationFst f hL d V c).left := by
  let e := (Over.forget _).mapIso (variableChartRelationSwapIso f hL d V c)
  have h : e.hom ≫ (variableChartRelationSnd f hL d V c).left =
      (variableChartRelationFst f hL d V c).left :=
    congrArg Over.Hom.left (variableChartEquivalenceRelation f hL d V c).symmetry₂
  rw [← h]
  infer_instance

end FLT.Mazur.HilbertChart
