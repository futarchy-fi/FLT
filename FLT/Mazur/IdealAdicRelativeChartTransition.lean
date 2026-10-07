/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSchemeCover

/-!
# Original restriction maps are the relative chart transitions

The spectrum of the original relative restriction commutes with both
projections and with the chart inclusion into the changed-base scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)
variable {U V : X.affineOpens} (i : U.1 ⟶ V.1)

/-- The spectrum of the original relative restriction. -/
def relativeTensorTransition :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    Spec (.of (RelativeAlgebra J f U)) ⟶ Spec (.of (RelativeAlgebra J f V)) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact Spec.map (CommRingCat.ofHom (relativeRestriction J f i).toRingHom)

/-- The transition preserves the original graded-base projection. -/
@[reassoc]
lemma relativeTensorTransition_toBase :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeTensorTransition J f i ≫ relativeTensorToBase J f V =
      relativeTensorToBase J f U := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (relativeRestriction J f i).comp_algebraMap

/-- The transition preserves the original closed-coordinate projection. -/
@[reassoc]
lemma relativeTensorTransition_toChart :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeTensorTransition J f i ≫ relativeTensorToChart J f V =
      relativeTensorToChart J f U ≫
        Spec.map (CommRingCat.ofHom (closedScalarRestriction (J.comap f) i)) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

omit [IsLocallyNoetherian Y] in
/-- Closed chart inclusions commute with the actual closed restriction. -/
@[reassoc]
lemma closedAffineChart_restrict :
    Spec.map (CommRingCat.ofHom (closedScalarRestriction (J.comap f) i)) ≫
      (closedAffineChart J f V).2.fromSpec = (closedAffineChart J f U).2.fromSpec :=
  (closedAffineChart J f V).2.map_fromSpec (closedAffineChart J f U).2
    (((TopologicalSpace.Opens.map (J.comap f).subschemeι.base).map i).op)

/-- The original tensor restriction is exactly the transition between the scheme charts. -/
@[reassoc]
lemma relativeTensorTransition_chart :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeTensorTransition J f i ≫ relativeTensorChart J f V = relativeTensorChart J f U := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  apply (relativeScheme_isPullback J f).hom_ext
  · rw [Category.assoc, relativeTensorChart_toBase, relativeTensorChart_toBase,
      relativeTensorTransition_toBase]
  · rw [Category.assoc, relativeTensorChart_toClosed, relativeTensorChart_toClosed,
      relativeTensorTransition_toChart_assoc, closedAffineChart_restrict]

end FLT.Mazur.IdealAdicGradedPullback
