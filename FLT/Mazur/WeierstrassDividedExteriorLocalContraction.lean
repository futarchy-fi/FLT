/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundaryPullback
public import FLT.Mazur.WeierstrassDividedExteriorReassociation
public import FLT.Mazur.SchemeOpenReplacementPreimage

/-!
# The actual contraction after reassociating the exterior gluing

The map obtained by gluing the local contraction to the retained exterior
is exactly the already constructed step contraction under `advanceIso`.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))
open WeierstrassSuccessiveX

/-- The normalized local contraction retains the existing x-chart map. -/
@[reassoc] theorem xChart_localContraction :
    xChart W (π ^ k) π e.b3 e.b4 e.b6 ≫ localContraction hπ d e =
      xContraction hπ d e := by
  rw [localContraction, depthContraction, xChart_contraction_assoc]
  rfl

/-- The normalized deeper chart retains the existing depth transition. -/
@[reassoc] theorem depthDividedChart_localContraction :
    depthDividedChart π k W e.b3 e.b4 e.b6 ≫ localContraction hπ d e =
      transition hπ d e :=
  depthDividedChart_contraction π k hπ W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
    d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

/-- The actual local contraction glued to the identity on the unchanged exterior. -/
def Exterior.localReplacementContraction : E.localReplacement hπ e ⟶ E.whole :=
  SchemeOpenReplacement.contraction E.attach (boundaryInclusion d) (localBoundary hπ d e)
    (localContraction hπ d e) (localBoundary_contraction hπ d e)

/-- The replacement contraction is unchanged on the entire retained exterior. -/
@[reassoc (attr := simp)] theorem Exterior.localReplacement_inl_contraction :
    pushout.inl E.attach (localBoundary hπ d e) ≫ E.localReplacementContraction hπ e =
      E.exteriorChart := pushout.inl_desc _ _ _

/-- The replacement contraction restricts to the actual normalized local contraction. -/
@[reassoc (attr := simp)] theorem Exterior.localReplacement_inr_contraction :
    pushout.inr E.attach (localBoundary hπ d e) ≫ E.localReplacementContraction hπ e =
      localContraction hπ d e ≫ E.dividedChart := pushout.inr_desc _ _ _

/-- The reassociation retains the whole new x-direction chart. -/
@[reassoc] theorem Exterior.advanceIso_newX :
    E.newX hπ e ≫ (E.advance hπ e).exteriorChart ≫ (E.advanceIso hπ e).hom =
      xChart W (π ^ k) π e.b3 e.b4 e.b6 ≫
        pushout.inr E.attach (localBoundary hπ d e) := by
  simp [Exterior.advanceIso, Exterior.advanceNormalization, Iso.trans_hom,
    Exterior.exteriorChart, Exterior.newX, localBoundary, xChart]

/-- Reassociation preserves the actual whole step contraction. -/
@[reassoc] theorem Exterior.advanceIso_contraction :
    (E.advanceIso hπ e).hom ≫ E.localReplacementContraction hπ e =
      E.stepContraction hπ e := by
  apply Exterior.hom_ext
  · apply pushout.hom_ext
    · change E.retained hπ e ≫ (E.advance hπ e).exteriorChart ≫
        (E.advanceIso hπ e).hom ≫ E.localReplacementContraction hπ e =
          E.retained hπ e ≫ (E.advance hπ e).exteriorChart ≫ E.stepContraction hπ e
      rw [Exterior.advanceIso_retained_assoc, Exterior.retained_whole_contraction]
      exact E.localReplacement_inl_contraction hπ e
    · change E.newX hπ e ≫ (E.advance hπ e).exteriorChart ≫
        (E.advanceIso hπ e).hom ≫ E.localReplacementContraction hπ e =
          E.newX hπ e ≫ (E.advance hπ e).exteriorChart ≫ E.stepContraction hπ e
      rw [Exterior.advanceIso_newX_assoc, Exterior.localReplacement_inr_contraction]
      simp only [Exterior.exteriorChart_stepContraction, Exterior.newX_contraction]
      exact xChart_localContraction_assoc hπ e E.dividedChart
  · rw [← Category.assoc, Exterior.advanceIso_divided, Category.assoc]
    erw [E.localReplacement_inr_contraction hπ e]
    rw [← Category.assoc, depthDividedChart_localContraction,
      Exterior.dividedChart_stepContraction]


end FLT.Mazur.WeierstrassDividedDepth
