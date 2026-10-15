/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphCubic
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphClosedLift
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphChartBranch

/-!
# The full finite branch graph maps into the actual original cubic graph chart

Both original node coordinates construct a point of the cubic relation.
Schematic density of the two punctures extends their actual graph membership
to the full finite graph. This is a comparison morphism, not an isomorphism
or a transfer of flatness from the literal graph chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "E" => completeIdentityFirstGraphScheme K n h (0 : Fin n)
local notation "s" => completeIdentityFirstGraphSchemeSource K n h (0 : Fin n) ≫
  Iso.hom (firstNodeParameterIso K)
local notation "d" => completeIdentityFirstGraphSchemeTarget K n h (0 : Fin n) ≫
  Spec.map (CommRingCat.ofHom (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _)))
local notation "j" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0

/-- The full finite graph satisfies the original node-pair cubic relation. -/
def completeIdentityFirstGraphToChartSpace :
    (E) ⟶ completeIdentityActionAdicChartSpace K n h 1 0 0 :=
  pullback.lift (s) (d) (by
    simpa only [completeIdentityFirstGraphOriginalSource,
      completeIdentityFirstGraphOriginalTarget, Category.assoc] using
      (completeIdentityFirstGraphOriginalNodes_cubic K n h).symm)

/-- The left original graph branch has exactly this whole-graph node pair. -/
@[reassoc] theorem completeIdentityFirstGraphToChartSpace_left :
    completeIdentityFirstLeftToGraphChart K n h ≫ (j) =
      completeIdentityFirstGraphLeftBranch K n h 0 ≫
        completeIdentityFirstGraphToChartSpace K n h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityFirstGraphToChartSpace, pullback.lift_fst]
    exact completeIdentityFirstLeftToGraphChart_source K n h
  · simp only [Category.assoc, completeIdentityFirstGraphToChartSpace, pullback.lift_snd]
    exact completeIdentityFirstLeftToGraphChart_target K n h

/-- The actual incoming graph branch retains the same full original node pair. -/
@[reassoc] theorem completeIdentityFirstGraphToChartSpace_right :
    completeIdentityFirstRightToGraphChart K n h ≫ (j) =
      completeIdentityFirstGraphRightBranch K n h 0 ≫
        completeIdentityFirstGraphToChartSpace K n h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityFirstGraphToChartSpace, pullback.lift_fst]
    exact completeIdentityFirstRightToGraphChart_source K n h
  · simp only [Category.assoc, completeIdentityFirstGraphToChartSpace, pullback.lift_snd]
    exact completeIdentityFirstRightToGraphChart_target K n h

/-- Both punctures' actual graph membership extends to the entire nonreduced finite graph. -/
def completeIdentityFirstGraphToChart :
    (E) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0 :=
  completeIdentityFirstGraphClosedLift K n h 0 (j)
    (completeIdentityFirstGraphToChartSpace K n h)
    (completeIdentityFirstLeftToGraphChart K n h)
    (completeIdentityFirstRightToGraphChart K n h)
    (completeIdentityFirstGraphToChartSpace_left K n h)
    (completeIdentityFirstGraphToChartSpace_right K n h)

/-- The comparison retains the original full closed graph embedding. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_embedding :
    completeIdentityFirstGraphToChart K n h ≫ (j) =
      completeIdentityFirstGraphToChartSpace K n h :=
  completeIdentityFirstGraphClosedLift_fac _ _ _ _ _ _ _ _ _ _

/-- Its source coordinate is exactly the original finite-graph source and parameter isomorphism. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_source :
    completeIdentityFirstGraphToChart K n h ≫
      completeIdentityActionGraphAdicChartSource K n h 1 0 0 = (s) := by
  rw [completeIdentityActionGraphAdicChartSource,
    completeIdentityFirstGraphToChart_embedding_assoc]
  exact pullback.lift_fst _ _ _

/-- Its target coordinate is the original finite-graph target with the unchanged scalar map. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_target :
    completeIdentityFirstGraphToChart K n h ≫
      completeIdentityActionGraphAdicChartTarget K n h 1 0 0 = (d) := by
  rw [completeIdentityActionGraphAdicChartTarget,
    completeIdentityFirstGraphToChart_embedding_assoc]
  exact pullback.lift_snd _ _ _

/-- The comparison is finite over the actual affine chart, without any assumed flatness. -/
instance completeIdentityFirstGraphToChart_finite :
    IsFinite (completeIdentityFirstGraphToChart K n h) := by
  let _ : IsFinite (completeIdentityFirstGraphToChart K n h ≫
      completeIdentityActionGraphAdicChartSource K n h 1 0 0) := by
    rw [completeIdentityFirstGraphToChart_source]
    infer_instance
  exact IsFinite.of_comp _ (completeIdentityActionGraphAdicChartSource K n h 1 0 0)

end FLT.Mazur.PolygonInfinitesimalStages
