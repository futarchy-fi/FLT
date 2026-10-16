/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchExtraction

/-!
# The original pole secant coefficient does not vanish at the source node

Its image is the fifth power of the actual common marking unit wherever
the original scaled source coordinate is zero. Thus the extra principal
neighborhood contains the source node, including all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "u" => completePointStageCommonMarkingUnit K n h 1 (0 : Fin n)
local notation "v" => (Q) ((η) ((ρ) ((u : Ring K 1) ^ 5)))
local notation "x" => (η) (leftCoordinate (t))
local notation "F" => completeIdentityFirstPoleCombination K n h
local notation "c" => completeIdentityFirstPoleSecantCoefficient K n h U

/-- The retained extraction coefficient is a unit in the actual common patch. -/
theorem completeIdentityFirstPolePatch_unit : IsUnit (v) :=
  ((((u).isUnit.pow 5).map (ρ)).map (η)).map (Q)

/-- Every node specialization kills the unchanged scaled source pole combination. -/
theorem completeIdentityFirstPolePatch_combination_node
    {T : Type*} [CommRing T] (f : (Z) →+* T) (hx : f ((S) (x)) = 0) :
    f ((S) (F)) = 0 :=
  NodePoleSecant.combination_node f _ _ _
    (completeIdentityFirstPolePatch_source_extract K n h U) hx

/-- Its secant coefficient specializes to the same actual fifth marking unit. -/
theorem completeIdentityFirstPolePatch_coefficient_node
    {T : Type*} [CommRing T] (f : (Z) →+* T) (hx : f ((S) (x)) = 0) :
    f (c) = f (v) :=
  NodePoleSecant.coefficient_node f _ _ _ _
    (completeIdentityFirstPolePatch_source_extract K n h U) hx

/-- The coefficient stays invertible under every such node specialization. -/
theorem completeIdentityFirstPolePatch_coefficient_node_isUnit
    {T : Type*} [CommRing T] (f : (Z) →+* T) (hx : f ((S) (x)) = 0) :
    IsUnit (f (c)) := by
  rw [completeIdentityFirstPolePatch_coefficient_node K n h U f hx]
  exact (completeIdentityFirstPolePatch_unit K n h U).map f

/-- No proper node ideal contains the actual secant coefficient. -/
theorem completeIdentityFirstPolePatch_coefficient_not_mem
    (I : Ideal (Z)) (hI : I ≠ ⊤) (hx : (S) (x) ∈ I) : (c) ∉ I := by
  intro hc
  have hu := completeIdentityFirstPolePatch_coefficient_node_isUnit K n h U
    (Ideal.Quotient.mk I) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc] at hu
  have hzero : (0 : (Z) ⧸ I) = 1 := isUnit_zero_iff.mp hu
  apply hI
  apply Ideal.eq_top_of_isUnit_mem I ?_ isUnit_one
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_one (Ideal.Quotient.mk I)).trans hzero.symm)

end FLT.Mazur.PolygonInfinitesimalStages
