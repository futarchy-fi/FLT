/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCoefficientAffineSheaf

/-!
# Actual closed coefficients and their affine grading

The closed-to-ambient comparison followed by the canonical chart map is an
isomorphism on every affine open. Its inverse gives the original closed
homogeneous coefficients, with finite support, for each glued section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedPullback

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual closed comparison is invertible on the whole affine basis. -/
instance closedCoefficientChartMap_isIso : IsIso (closedCoefficientChartMap J f) := by
  unfold closedCoefficientChartMap
  infer_instance

/-- Glued sections on an affine open are the direct sum of the original closed coefficients. -/
def closedCoefficientChartIso (U : X.affineOpens) :
    AddCommGrpCat.of (Total (J.comap f) U.1) ≅
      coefficientForget.obj ((coefficientRingSheaf J f).obj.obj (.op U.1)) :=
  (asIso (closedCoefficientChartMap J f)).app (.op U)

/-- Extract all original closed homogeneous components of an affine glued section. -/
def closedChartDecomposition (U : X.affineOpens)
    (s : (coefficientRingSheaf J f).obj.obj (.op U.1)) : Total (J.comap f) U.1 :=
  (closedCoefficientChartIso J f U).inv s

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Recombining the extracted closed homogeneous components recovers the original section. -/
lemma closedChartDecomposition_recombine (U : X.affineOpens)
    (s : (coefficientRingSheaf J f).obj.obj (.op U.1)) :
    (closedCoefficientChartMap J f).app (.op U) (closedChartDecomposition J f U s) = s := by
  change (closedCoefficientChartIso J f U).hom
    ((closedCoefficientChartIso J f U).inv s) = s
  have h := ConcreteCategory.congr_hom (closedCoefficientChartIso J f U).inv_hom_id s
  exact h

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Extraction preserves every original closed homogeneous insertion. -/
lemma closedChartDecomposition_of (U : X.affineOpens) (n : ℕ)
    (s : ClosedPiece (J.comap f) U.1 n) :
    closedChartDecomposition J f U
        ((closedCoefficientChartMap J f).app (.op U)
          (DirectSum.of (ClosedPiece (J.comap f) U.1) n s)) =
      DirectSum.of (ClosedPiece (J.comap f) U.1) n s :=
  ConcreteCategory.congr_hom (closedCoefficientChartIso J f U).hom_inv_id _

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The grading of each actual affine glued section has finite support. -/
lemma closedChartDecomposition_finite_support (U : X.affineOpens)
    (s : (coefficientRingSheaf J f).obj.obj (.op U.1)) :
    Set.Finite {n | closedChartDecomposition J f U s n ≠ 0} := by
  classical
  apply (closedChartDecomposition J f U s).support.finite_toSet.subset
  intro n hn
  exact DFinsupp.mem_support_iff.mpr hn

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The affine decomposition commutes with the original closed restrictions. -/
lemma closedChartDecomposition_restrict {U V : X.affineOpens} (i : U ⟶ V)
    (s : (coefficientRingSheaf J f).obj.obj (.op V.1)) :
    closedChartDecomposition J f U
        ((coefficientRingSheaf J f).obj.map ((AffineBasis.inclusion X).map i).op s) =
      totalRestriction (J.comap f) ((AffineBasis.inclusion X).map i)
        (closedChartDecomposition J f V s) := by
  have h := (asIso (closedCoefficientChartMap J f)).inv.naturality i.op
  exact ConcreteCategory.congr_hom h s

end FLT.Mazur.IdealAdicGradedClosedAction
