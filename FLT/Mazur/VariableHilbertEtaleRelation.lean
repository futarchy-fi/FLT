/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelationOperations
public import FLT.Mazur.BaseMarkedHilbertFullIntersection

/-!
# The full original relation over an étale translation base

Both projections of the original equal-Picard-class relation are étale. Its
reflexive locus is open, but the full relation still includes distinct base
maps. These facts concern the actual scheme relation, not a diagonal substitute.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Swapping the actual full relation is a scheme isomorphism. -/
def variableChartRelationSwapIso :
    variableChartRelation f hL d V c ≅ variableChartRelation f hL d V c where
  hom := variableChartRelationSwap f hL d V c
  inv := variableChartRelationSwap f hL d V c
  hom_inv_id := variableChartRelationSwap_involutive f hL d V c
  inv_hom_id := variableChartRelationSwap_involutive f hL d V c

instance variableChartRelationSnd_etale [Etale V.hom] :
    Etale (variableChartRelationSnd f hL d V c).left :=
  variableHilbertOverlapToTest_etale f d V _ c _

instance variableChartRelationFst_etale [Etale V.hom] :
    Etale (variableChartRelationFst f hL d V c).left := by
  let e := (Over.forget _).mapIso (variableChartRelationSwapIso f hL d V c)
  have h : e.hom ≫ (variableChartRelationSnd f hL d V c).left =
      (variableChartRelationFst f hL d V c).left :=
    congrArg Over.Hom.left (variableChartEquivalenceRelation f hL d V c).symmetry₂
  rw [← h]
  infer_instance

/-- The actual reflexive locus is open in the full relation, not assumed to be all of it. -/
instance variableChartRelationRefl_isOpenImmersion [Etale V.hom] :
    IsOpenImmersion (variableChartRelationRefl f hL d V c).left :=
  UnramifiedSectionImmersion.isOpenImmersion (variableChartRelationSnd f hL d V c).left
    (variableChartRelationRefl f hL d V c).left
    (congrArg Over.Hom.left (variableChartEquivalenceRelation f hL d V c).reflexivity₂)

end FLT.Mazur.HilbertChart
