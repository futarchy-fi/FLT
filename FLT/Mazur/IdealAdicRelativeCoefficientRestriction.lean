/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeChartTransition

/-!
# The original coefficient restrictions over relative chart transitions

The original total coefficient restriction is semilinear over the original
tensor-ring transition. It preserves multiplication and the closed homogeneous
coefficients, and its identity and composition laws use the actual maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual restriction is semilinear over the original relative tensor-ring restriction. -/
def relativeCoefficientRestriction {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    relativeChartCoefficient J f V →ₛₗ[(relativeRestriction J f i).toRingHom]
      relativeChartCoefficient J f U := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  refine { restrict (J.comap f) U.1 i with map_smul' := ?_ }
  intro r s
  change IdealAdicGradedSections.Sections (J.comap f) V.1 at s
  change restrictRingHom (J.comap f) U.1 i (relativeMap J f V r * s) =
    relativeMap J f U (relativeRestriction J f i r) * restrictRingHom (J.comap f) U.1 i s
  rw [map_mul, relativeMap_restrict]

/-- The new semilinear interface retains the original graded-ring restriction. -/
lemma relativeCoefficientRestriction_apply {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s : IdealAdicGradedSections.Sections (J.comap f) V.1) :
    relativeCoefficientRestriction J f i s = restrictRingHom (J.comap f) U.1 i s := rfl

/-- Restriction retains multiplication of original coefficients. -/
lemma relativeCoefficientRestriction_mul {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s t : IdealAdicGradedSections.Sections (J.comap f) V.1) :
    relativeCoefficientRestriction J f i (s * t) =
      @Mul.mul (IdealAdicGradedSections.Sections (J.comap f) U.1) inferInstance
        (relativeCoefficientRestriction J f i s) (relativeCoefficientRestriction J f i t) :=
  map_mul (restrictRingHom (J.comap f) U.1 i) s t

/-- The semilinear restriction retains the actual closed total restriction. -/
lemma relativeCoefficientRestriction_closed {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s : Total (J.comap f) V.1) :
    relativeCoefficientRestriction J f i (totalEquiv (J.comap f) V.1 s) =
      totalEquiv (J.comap f) U.1 (totalRestriction (J.comap f) i s) :=
  (totalEquiv_restrict (J.comap f) i s).symm

/-- Every original closed homogeneous section restricts within its degree. -/
lemma relativeCoefficientRestriction_closed_of {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (n : ℕ) (s : ClosedPiece (J.comap f) V.1 n) :
    relativeCoefficientRestriction J f i
        (of (J.comap f) V.1 n (pieceEquiv (J.comap f) V.1 n s)) =
      of (J.comap f) U.1 n (pieceEquiv (J.comap f) U.1 n
        (pieceRestriction (J.comap f) i n s)) := by
  rw [relativeCoefficientRestriction_apply]
  exact (restrict_of (J.comap f) U.1 i n _).trans
    (congrArg (of (J.comap f) U.1 n) (pieceEquiv_restrict (J.comap f) i n s).symm)

/-- Identity transition fixes every actual coefficient. -/
lemma relativeCoefficientRestriction_id (U : X.affineOpens)
    (s : IdealAdicGradedSections.Sections (J.comap f) U.1) :
    relativeCoefficientRestriction J f (𝟙 U.1) s = s :=
  RingHom.congr_fun (restrict_id (J.comap f) U.1) s

/-- Actual coefficient restrictions obey the overlap composition law. -/
lemma relativeCoefficientRestriction_comp {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1)
    (s : IdealAdicGradedSections.Sections (J.comap f) W.1) :
    relativeCoefficientRestriction J f i (relativeCoefficientRestriction J f j s) =
      relativeCoefficientRestriction J f (i ≫ j) s :=
  RingHom.congr_fun (restrict_comp (J.comap f) i j) s

end FLT.Mazur.IdealAdicGradedPullback
