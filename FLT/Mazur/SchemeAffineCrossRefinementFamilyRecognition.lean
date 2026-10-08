/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamilyNormalization

/-!
# Recognition of the pairwise comparisons in a simultaneous refinement

Faithful reconstruction identifies the coherent family comparisons with the
existing pairwise cross-refinement comparisons. Their cocycle therefore holds
for the actual pair objects used by the affine overlap construction.
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
attribute [local irreducible] Chart.comparison Chart.reconstruction
  Chart.refinementReconstruction effectiveComparison CrossRefinement.effectiveComparison

/-- Faithful reconstruction identifies the family comparison with the existing pair. -/
theorem effectiveComparison_eq_pair (i j : ι) :
    ρ.effectiveComparison D i j = (ρ.pair i j).effectiveComparison D := by
  apply Iso.ext
  apply (ρ.pair i j).effectiveComparison_unique D
  rw [ρ.pair_left_refinementReconstruction D i j,
    ρ.pair_right_refinementReconstruction D i j]
  exact ρ.effectiveComparison_reconstruction D i j

/-- Actual pairwise effective comparisons satisfy the simultaneous-refinement cocycle. -/
theorem pair_effectiveComparison_cocycle (i j k : ι) :
    ((ρ.pair i j).effectiveComparison D).hom ≫
        ((ρ.pair j k).effectiveComparison D).hom =
      ((ρ.pair i k).effectiveComparison D).hom := by
  rw [← ρ.effectiveComparison_eq_pair D i j, ← ρ.effectiveComparison_eq_pair D j k,
    ← ρ.effectiveComparison_eq_pair D i k]
  exact ρ.effectiveComparison_cocycle D i j k

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
