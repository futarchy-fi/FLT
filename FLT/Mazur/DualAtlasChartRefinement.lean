/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFreeDualProjectiveAtlas

/-!
# Original dual atlas inclusions under refinement

The inclusions into the actual glued atlas obey their defining colimit laws.
Their ranges contain exactly the points over the original source opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFreeDualProjectiveAtlas
open FCurve AffineFiniteFreeAtlas FiniteFreeChartTransitions
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)

/-- Original chart refinements preserve their inclusions into the glued atlas. -/
@[reassoc]
lemma chart_refinement {i j : Index M} (h : i ≤ j) :
    dualChartInclusion M h (chart M i) (chart M j) ≫ chartMap M hM j =
      chartMap M hM i :=
  colimit.w (gluingData M hM).functor (homOfLE h)

/-- Every atlas point over an original open lifts to that original projective chart. -/
lemma exists_chart_preimage (i : Index M) (x : space M hM)
    (hx : projection M hM x ∈ i.val) :
    ∃ y, chartMap M hM i y = x := by
  have hy : x ∈ projection M hM ⁻¹ᵁ i.val := hx
  rw [projection_preimage] at hy
  exact hy

end FLT.Mazur.LocallyFreeDualProjectiveAtlas
