/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorLocalContraction
public import FLT.Mazur.WeierstrassSuccessiveDepthProper
public import FLT.Mazur.SchemeOpenReplacementProper

/-!
# Proper whole contraction for an arbitrary retained exterior

The local Rees contraction is proper. Its complete boundary pullback allows
properness to be glued over both target charts, and reassociation transfers
this to the already constructed exterior step contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))

/-- Properness of the actual normalized local map, with coefficient data bundled. -/
theorem localContraction_isProper : IsProper (localContraction hπ d e) :=
  WeierstrassSuccessiveX.depthContraction_isProper π k hπ W d.b3 d.b4 d.b6
    e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

/-- The whole replacement restricts to the identity over the full old exterior. -/
theorem Exterior.localReplacement_exterior_isPullback :
    IsPullback (𝟙 E.carrier) (pushout.inl E.attach (localBoundary hπ d e))
      E.exteriorChart (E.localReplacementContraction hπ e) :=
  SchemeOpenReplacement.isPullback_inl E.attach (boundaryInclusion d) (localBoundary hπ d e)
    (localContraction hπ d e) (localBoundary_contraction hπ d e) (localBoundary_preimage hπ d e)

/-- The full inverse image of the old divided chart is the actual local modification. -/
theorem Exterior.localReplacement_divided_isPullback :
    IsPullback (localContraction hπ d e) (pushout.inr E.attach (localBoundary hπ d e))
      E.dividedChart (E.localReplacementContraction hπ e) :=
  SchemeOpenReplacement.isPullback_inr E.attach (boundaryInclusion d) (localBoundary hπ d e)
    (localContraction hπ d e) (localBoundary_contraction hπ d e)

/-- Gluing the local modification into any retained exterior gives a proper whole map. -/
theorem Exterior.localReplacementContraction_isProper :
    IsProper (E.localReplacementContraction hπ e) := by
  let _ := localContraction_isProper hπ (d := d) e
  exact SchemeOpenReplacement.contraction_isProper E.attach (boundaryInclusion d)
    (localBoundary hπ d e) (localContraction hπ d e) (localBoundary_contraction hπ d e)
    (localBoundary_preimage hπ d e)

/-- The existing exterior advance contracts properly to its preceding whole scheme. -/
theorem Exterior.stepContraction_isProper : IsProper (E.stepContraction hπ e) := by
  rw [← E.advanceIso_contraction hπ e]
  let _ := E.localReplacementContraction_isProper hπ e
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
