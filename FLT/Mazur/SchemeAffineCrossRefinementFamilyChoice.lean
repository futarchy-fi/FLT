/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamilyRecognition
public import FLT.Mazur.SchemeAffineCrossRefinementBaseChoice
/-!
# Cocycles for independently chosen pair covers

Cover choice independence transfers the simultaneous family cocycle to the separately
constructed canonical covers of each pair of charts.
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
attribute [local irreducible] CrossRefinement.effectiveComparison

/-- Independent canonical pair covers give the simultaneous pair comparison. -/
theorem pair_effectiveComparison_eq_canonical (i j : ι) :
    ((ρ.pair i j).effectiveComparison D).hom =
      (((C i).commonBaseCrossRefinement (C j) (ρ.baseMap i) (ρ.baseMap j)
        ((ρ.base_over i).trans (ρ.base_over j).symm)).effectiveComparison D).hom := by
  exact eq_of_heq ((ρ.pair i j).effectiveComparison_cover_choice_independent
    ((C i).commonBaseCrossRefinement (C j) (ρ.baseMap i) (ρ.baseMap j)
      ((ρ.base_over i).trans (ρ.base_over j).symm)) D rfl HEq.rfl HEq.rfl)

/-- Comparisons constructed with independent canonical pair covers satisfy the cocycle. -/
theorem canonical_effectiveComparison_cocycle (i j k : ι) :
    (((C i).commonBaseCrossRefinement (C j) (ρ.baseMap i) (ρ.baseMap j)
        ((ρ.base_over i).trans (ρ.base_over j).symm)).effectiveComparison D).hom ≫
      (((C j).commonBaseCrossRefinement (C k) (ρ.baseMap j) (ρ.baseMap k)
        ((ρ.base_over j).trans (ρ.base_over k).symm)).effectiveComparison D).hom =
      (((C i).commonBaseCrossRefinement (C k) (ρ.baseMap i) (ρ.baseMap k)
        ((ρ.base_over i).trans (ρ.base_over k).symm)).effectiveComparison D).hom := by
  rw [← ρ.pair_effectiveComparison_eq_canonical D i j,
    ← ρ.pair_effectiveComparison_eq_canonical D j k,
    ← ρ.pair_effectiveComparison_eq_canonical D i k]
  exact ρ.pair_effectiveComparison_cocycle D i j k
end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
