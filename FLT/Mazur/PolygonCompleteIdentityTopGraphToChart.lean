/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphCubic
public import FLT.Mazur.PolygonTopNodeGraphClosedLift
public import FLT.Mazur.PolygonCompleteIdentityTopGraphChartBranch

/-!
# The full finite branch graph maps into the actual original cubic graph chart

Both original node coordinates construct a point of the cubic relation.
Schematic density of the two punctures extends their actual graph membership
to the full higher graph. This is a comparison morphism, not an isomorphism
or a transfer of flatness from the literal graph chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "E" => completeIdentityTopGraphScheme K n h (0 : Fin n) m
local notation "s" => completeIdentityTopGraphSchemeSource K n h (0 : Fin n) m ≫
  Iso.hom (stageNodeParameterIso K (m + 1))
local notation "d" => completeIdentityTopGraphSchemeTarget K n h (0 : Fin n) m ≫
  Spec.map (CommRingCat.ofHom (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _)))
local notation "j" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0

/-- The full higher graph satisfies the original node-pair cubic relation. -/
def completeIdentityTopGraphToChartSpace :
    (E) ⟶ completeIdentityActionAdicChartSpace K n h (m + 1) 0 0 :=
  pullback.lift (s) (d) (by
    simpa only [completeIdentityTopGraphOriginalSource,
      completeIdentityTopGraphOriginalTarget, Category.assoc] using
      (completeIdentityTopGraphOriginalNodes_cubic K n h m).symm)

/-- The left original graph branch has exactly this whole-graph node pair. -/
@[reassoc] theorem completeIdentityTopGraphToChartSpace_left :
    completeIdentityTopLeftToGraphChart K n h m ≫ (j) =
      completeIdentityTopGraphLeftBranch K n h 0 m ≫
        completeIdentityTopGraphToChartSpace K n h m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityTopGraphToChartSpace, pullback.lift_fst]
    exact completeIdentityTopLeftToGraphChart_source K n h m
  · simp only [Category.assoc, completeIdentityTopGraphToChartSpace, pullback.lift_snd]
    exact completeIdentityTopLeftToGraphChart_target K n h m

/-- The actual incoming graph branch retains the same full original node pair. -/
@[reassoc] theorem completeIdentityTopGraphToChartSpace_right :
    completeIdentityTopRightToGraphChart K n h m ≫ (j) =
      completeIdentityTopGraphRightBranch K n h 0 m ≫
        completeIdentityTopGraphToChartSpace K n h m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityTopGraphToChartSpace, pullback.lift_fst]
    exact completeIdentityTopRightToGraphChart_source K n h m
  · simp only [Category.assoc, completeIdentityTopGraphToChartSpace, pullback.lift_snd]
    exact completeIdentityTopRightToGraphChart_target K n h m

/-- Both punctures' actual graph membership extends to the entire nonreduced higher graph. -/
def completeIdentityTopGraphToChart :
    (E) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  topNodeGraphClosedLift K[T;T⁻¹] m
    (completeIdentityTopActionUnit K n h 0 m)
    (completeIdentityTopActionReciprocalUnit K n h 0 m) (j)
    (completeIdentityTopGraphToChartSpace K n h m)
    (completeIdentityTopLeftToGraphChart K n h m)
    (completeIdentityTopRightToGraphChart K n h m)
    (completeIdentityTopGraphToChartSpace_left K n h m)
    (completeIdentityTopGraphToChartSpace_right K n h m)

/-- The comparison retains the original full closed graph embedding. -/
@[reassoc] theorem completeIdentityTopGraphToChart_embedding :
    completeIdentityTopGraphToChart K n h m ≫ (j) =
      completeIdentityTopGraphToChartSpace K n h m :=
  topNodeGraphClosedLift_fac _ _ _ _ _ _ _ _ _ _

/-- Its source coordinate is exactly the original finite-graph source and parameter isomorphism. -/
@[reassoc] theorem completeIdentityTopGraphToChart_source :
    completeIdentityTopGraphToChart K n h m ≫
      completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 = (s) := by
  rw [completeIdentityActionGraphAdicChartSource,
    completeIdentityTopGraphToChart_embedding_assoc]
  exact pullback.lift_fst _ _ _

/-- Its target coordinate is the original finite-graph target with the unchanged scalar map. -/
@[reassoc] theorem completeIdentityTopGraphToChart_target :
    completeIdentityTopGraphToChart K n h m ≫
      completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 = (d) := by
  rw [completeIdentityActionGraphAdicChartTarget,
    completeIdentityTopGraphToChart_embedding_assoc]
  exact pullback.lift_snd _ _ _

/-- The preceding original law proves finiteness over the actual affine chart. -/
theorem completeIdentityTopGraphToChart_finite
    (hm : completeIdentityFiniteMulDefect K n h 0 m = 0) :
    IsFinite (completeIdentityTopGraphToChart K n h m) := by
  let _ := completeIdentityTopGraphSchemeSource_finite K n h 0 m hm
  let _ : IsFinite (completeIdentityTopGraphToChart K n h m ≫
      completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0) := by
    rw [completeIdentityTopGraphToChart_source]
    infer_instance
  exact IsFinite.of_comp _ (completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0)

end FLT.Mazur.PolygonInfinitesimalStages
