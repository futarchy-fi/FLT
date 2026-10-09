/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartTripleTransition

/-!
# The Hilbert chart gluing cocycle

Projection formulas for the actual triple maps prove the cyclic identity by
cancelling open inclusions. The self-overlap satisfies the gluing identity laws.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v z : Fin d → MvPolynomial I R)

/-- Three actual cyclic triple transitions compose to the identity. -/
theorem chartTupleTripleMap_cocycle :
    chartTupleTripleMap R I d w v z ≫ chartTupleTripleMap R I d v z w ≫
      chartTupleTripleMap R I d z w v = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (chartTupleTransitionOpen R I d w v).ι
    (chartTupleTransitionOpen R I d w z).ι ≫ (chartTupleTransitionOpen R I d w v).ι)).mp
  simp only [Category.assoc, Category.id_comp, chartTupleTripleMap_fst_assoc,
    chartTupleTripleComparison_ι, chartTupleTripleComparison_transition,
    chartTupleTripleMap_snd_assoc, chartTupleReverseMorphism_transition]

/-- The actual self-overlap map is the identity. -/
theorem chartTupleReverseMorphism_self : chartTupleReverseMorphism R I d w w = 𝟙 _ := by
  rw [← cancel_mono (chartTupleTransitionOpen R I d w w).ι,
    chartTupleReverseMorphism_ι, chartTupleTransition_self, Category.id_comp]

/-- The inclusion of the self-overlap is an isomorphism onto the whole chart. -/
instance chartTupleTransitionOpen_self_isIso : IsIso (chartTupleTransitionOpen R I d w w).ι := by
  rw [chartTupleTransitionOpen_self]
  exact inferInstanceAs (IsIso (Spec (.of (ChartRing R I d w))).topIso.hom)

end FLT.Mazur.HilbertChart
