/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIteratedPullbackSections
public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Comparing affine and scheme overlap normalization

Express normalization by objectwise composite pullbacks using the natural
pullback comparison. Keeping the scheme maps abstract avoids expanding the
concrete tensor-spectrum sheaves while checking the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z T : Scheme.{u}}

/-- Objectwise pullback composition agrees with the natural path comparison. -/
theorem compositeIso_eq_comparison (f : T ⟶ Z) (g : Z ⟶ Y) (k : T ⟶ Y)
    (h : f ≫ g = k) (M : Y.Modules) :
    compositeIso f g k h M = (SheafPullbackPathComparison.comparison f g k h).app M := rfl

/-- Objectwise conjugation is the normalized scheme overlap transport. -/
theorem compositeIso_normalize (l r : Z ⟶ Y) (k : T ⟶ Z) (i j : T ⟶ Y)
    (hi : k ≫ l = i) (hj : k ≫ r = j) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M) :
    (compositeIso k l i hi M).symm ≪≫ (pullback k).mapIso e ≪≫
        compositeIso k r j hj M =
      SchemeOverlapDiagonalChart.normalize l r k i j hi hj M e := by
  simp only [compositeIso_eq_comparison, SchemeOverlapDiagonalChart.normalize]

end FLT.Mazur.AffineIteratedPullbackSections
