/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicAffineGeneration
public import FLT.Mazur.IdealAdicRelativeAffineSheaf
public import Mathlib.RingTheory.FiniteStability

/-!
# Noetherianity of the actual relative graded rings

Finite type of the actual base algebra survives tensoring with the closed
coordinate ring. The canonical chart isomorphism transfers Noetherianity
to the glued relative ring, rather than to a replacement ring.
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

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The actual closed coordinate ring on an ambient affine chart is Noetherian. -/
lemma closedScalars_isNoetherianRing : IsNoetherianRing (ClosedScalars (J.comap f) U.1) := by
  let _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_surjective Γ(X, U.1) _ ((J.comap f).subschemeι.app U.1).hom
    ((J.comap f).subschemeι_app_surjective U)

omit [IsLocallyNoetherian X] in
/-- The base-change algebra with closed scalars in the left tensor factor is finite type. -/
lemma relativeSwap_finiteType :
    let := closedBaseAlgebra J f U.1
    Algebra.FiniteType (ClosedScalars (J.comap f) U.1)
      (ClosedScalars (J.comap f) U.1 ⊗[Γ(Y, ⊤)] IdealAdicGradedSections.Sections J ⊤) := by
  let := closedBaseAlgebra J f U.1
  let _ : Algebra.FiniteType Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤) :=
    affineSections_finiteType J ⟨⊤, isAffineOpen_top _⟩
  infer_instance

/-- The original relative tensor ring is Noetherian. -/
lemma relativeAlgebra_isNoetherianRing :
    let := closedBaseAlgebra J f U.1
    IsNoetherianRing (RelativeAlgebra J f U) := by
  let := closedBaseAlgebra J f U.1
  let _ := closedScalars_isNoetherianRing J f U
  let _ := relativeSwap_finiteType J f U
  let _ : IsNoetherianRing
      (ClosedScalars (J.comap f) U.1 ⊗[Γ(Y, ⊤)] IdealAdicGradedSections.Sections J ⊤) :=
    Algebra.FiniteType.isNoetherianRing (ClosedScalars (J.comap f) U.1) _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm Γ(Y, ⊤) (ClosedScalars (J.comap f) U.1)
      (IdealAdicGradedSections.Sections J ⊤)).toRingEquiv

/-- Noetherianity holds for the actual glued relative ring on every affine chart. -/
lemma relativeSheaf_isNoetherianRing :
    IsNoetherianRing ((relativeScalarSheaf J f).obj.obj (.op U.1)) := by
  let := closedBaseAlgebra J f U.1
  let _ := relativeAlgebra_isNoetherianRing J f U
  exact isNoetherianRing_of_surjective (RelativeAlgebra J f U) _
    (relativeChartIso J f U).hom.hom
    (ConcreteCategory.bijective_of_isIso (relativeChartIso J f U).hom).surjective

end FLT.Mazur.IdealAdicGradedPullback
