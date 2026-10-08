/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamilyReconstruction
/-!
# Normalizing reconstruction maps of simultaneous refinements

The pairwise refinements and simultaneous refinements have the same covering
factorizations. Their reconstruction isomorphisms agree independently of the
chosen expression for the map of the common base into the original scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type v} {C : ι → Chart p}
variable (ρ : CrossRefinementFamily C) {M : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
attribute [local irreducible] Chart.reconstruction AffineRefinementPullback.reconstruction
  SheafPullbackPathComparison.comparison

/-- The left pair refinement reconstructs through the family factorization. -/
theorem pair_left_refinementReconstruction (i j : ι) :
    (C i).refinementReconstruction (ρ.pair i j).leftChart D
        (ρ.pair i j).leftRefinement =
      (C i).refinementReconstruction (ρ.chart i) D (ρ.refinement i) := by
  unfold Chart.refinementReconstruction
  rfl

/-- The right pair refinement reconstructs through the family factorization. -/
theorem pair_right_refinementReconstruction (i j : ι) :
    (C j).refinementReconstruction (ρ.pair i j).rightChart D
        (ρ.pair i j).rightRefinement =
      (C j).refinementReconstruction (ρ.chart j) D (ρ.refinement j) := by
  unfold Chart.refinementReconstruction
  rfl
end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
