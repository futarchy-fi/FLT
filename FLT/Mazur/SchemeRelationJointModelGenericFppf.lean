/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationJointModelGeometry
public import FLT.Mazur.SchemeGenericFppfTargetOpen

/-!
# Dominance and generic fppf geometry of actual joint coefficient models

Both coefficient systems remain in the original invariant ring. Injectivity
of their joint inclusion proves dominance. An integral original source also
makes the joint model integral, so its fppf region is dense and nonempty.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationJointModel
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {E A : Scheme.{0}} (p q : E ⟶ A)
  {C D : Type} [CommRing C] [CommRing D]
  (c : C →+* compatibleFunctions p q) (d : D →+* compatibleFunctions p q)

/-- Literal inclusion of the joint invariant coefficients makes its projection dominant. -/
instance projection_isDominant [CompactSpace A] : IsDominant (projection p q c d) :=
  isDominant_of_of_appTop_injective (projection_appTop_injective p q c d)

/-- Integrality is inherited from the unchanged original source, not from a reduced stratum. -/
instance target_isIntegral [IsIntegral A] : IsIntegral (target p q c d) := by
  change IsIntegral (Spec (.of (FiniteCoefficientJoin.algebra c d)))
  infer_instance

/-- An affine original source gives a quasi-compact whole-source joint projection. -/
instance projection_quasiCompact [IsAffine A] : QuasiCompact (projection p q c d) := by
  infer_instance

variable [IsIntegral A] [IsAffine A] [LocallyOfFinitePresentation (projection p q c d)]

/-- The actual joint fppf region is dense, without either coefficient model being effective. -/
theorem fppfLocus_dense :
    Dense (SchemeFppfTargetOpen.locus (projection p q c d) : Set (target p q c d)) :=
  SchemeFppfTargetOpen.dense (projection p q c d)

/-- In particular its complete original-source flat restriction has actual target points. -/
theorem fppfLocus_nonempty :
    (SchemeFppfTargetOpen.locus (projection p q c d) : Set (target p q c d)).Nonempty :=
  SchemeFppfTargetOpen.nonempty (projection p q c d)

end FLT.Mazur.SchemeRelationJointModel
