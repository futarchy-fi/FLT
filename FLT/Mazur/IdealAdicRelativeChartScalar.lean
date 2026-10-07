/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientRestriction

/-!
# Original chart scalars inside the relative tensor ring

Ambient chart coordinates map through the closed quotient and the right
tensor inclusion. Their action is the original coefficient scalar action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Actual ambient chart coordinates included in the right tensor factor via the closed quotient. -/
def relativeChartScalar (V : X.affineOpens) :
    let := closedBaseAlgebra J f V.1
    Γ(X, V.1) →+* RelativeAlgebra J f V := by
  let := closedBaseAlgebra J f V.1
  exact (Algebra.TensorProduct.includeRight (R := Γ(Y, ⊤))
    (A := IdealAdicGradedSections.Sections J ⊤)).toRingHom.comp
      ((J.comap f).subschemeι.app V.1).hom

/-- The chart scalar is the original pure tensor, retaining the actual closed quotient. -/
lemma relativeChartScalar_apply (V : X.affineOpens) (r : Γ(X, V.1)) :
    let := closedBaseAlgebra J f V.1
    relativeChartScalar J f V r =
      (1 : IdealAdicGradedSections.Sections J ⊤) ⊗ₜ[Γ(Y, ⊤)]
        (J.comap f).subschemeι.app V.1 r := rfl

/-- Original chart scalars commute with the actual relative-ring restrictions. -/
lemma relativeChartScalar_restrict {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (r : Γ(X, V.1)) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeRestriction J f i (relativeChartScalar J f V r) =
      relativeChartScalar J f U (X.presheaf.map i.op r) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  rw [relativeChartScalar_apply, relativeRestriction_tmul, relativeChartScalar_apply]
  congr 1
  exact (ConcreteCategory.congr_hom ((J.comap f).subschemeι.naturality i.op) r).symm

variable [IsLocallyNoetherian X] [IsAffine Y]

/-- The relative coefficient action of a chart coordinate is its original structural action. -/
lemma relativeChartScalar_smul (V : X.affineOpens) (r : Γ(X, V.1))
    (s : relativeChartCoefficient J f V) :
    let := closedBaseAlgebra J f V.1
    relativeChartScalar J f V r • s =
      r • (show IdealAdicGradedSections.Sections (J.comap f) V.1 from s) := by
  let := closedBaseAlgebra J f V.1
  let := localBaseAlgebra J f V.1
  change relativeMap J f V (relativeChartScalar J f V r) *
    (show IdealAdicGradedSections.Sections (J.comap f) V.1 from s) = _
  rw [relativeChartScalar_apply, relativeMap_tmul, one_smul, closedScalarAdd_quotient]
  exact (Algebra.smul_def r _).symm

/-- Actual coefficient restriction as a linear map after restricting target scalars. -/
def relativeCoefficientRestrictionLinear {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeChartCoefficient J f V →ₗ[RelativeAlgebra J f V]
      (ModuleCat.restrictScalars (relativeRestriction J f i).toRingHom).obj
        (relativeChartCoefficient J f U) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact { relativeCoefficientRestriction J f i with
    map_smul' := (relativeCoefficientRestriction J f i).map_smulₛₗ }

/-- The linear interface retains the actual graded coefficient restriction. -/
lemma relativeCoefficientRestrictionLinear_apply {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s : IdealAdicGradedSections.Sections (J.comap f) V.1) :
    relativeCoefficientRestrictionLinear J f i s = restrictRingHom (J.comap f) U.1 i s := rfl

end FLT.Mazur.IdealAdicGradedPullback
