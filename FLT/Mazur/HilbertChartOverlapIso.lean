/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartReverseTransition

/-!
# Actual isomorphisms between Hilbert chart overlaps

The two reverse-domain factorizations are inverse by cancellation of the
open inclusions. Thus each original transition is itself an open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- The two actual overlap maps are inverse on their full domains. -/
theorem chartTupleReverseMorphism_inverse :
    chartTupleReverseMorphism R I d w v ≫ chartTupleReverseMorphism R I d v w = 𝟙 _ := by
  rw [← cancel_mono (chartTupleTransitionOpen R I d w v).ι, Category.assoc,
    chartTupleReverseMorphism_ι, chartTupleReverseMorphism_transition, Category.id_comp]

/-- The actual isomorphism between the two chart overlap domains. -/
def chartTupleOverlapIso : (chartTupleTransitionOpen R I d w v).toScheme ≅
    (chartTupleTransitionOpen R I d v w).toScheme where
  hom := chartTupleReverseMorphism R I d w v
  inv := chartTupleReverseMorphism R I d v w
  hom_inv_id := chartTupleReverseMorphism_inverse R I d w v
  inv_hom_id := chartTupleReverseMorphism_inverse R I d v w

/-- The factorized change of tuple is an isomorphism. -/
instance chartTupleReverseMorphism_isIso : IsIso (chartTupleReverseMorphism R I d w v) :=
  inferInstanceAs (IsIso (chartTupleOverlapIso R I d w v).hom)

/-- The original transition into the second chart is an open immersion. -/
instance chartTupleTransition_isOpenImmersion :
    IsOpenImmersion (chartTupleTransition R I d w v) := by
  rw [← chartTupleReverseMorphism_ι R I d w v]
  infer_instance

/-- The overlap isomorphism followed by inclusion recovers the original transition. -/
theorem chartTupleOverlapIso_hom_ι :
    (chartTupleOverlapIso R I d w v).hom ≫ (chartTupleTransitionOpen R I d v w).ι =
      chartTupleTransition R I d w v :=
  chartTupleReverseMorphism_ι R I d w v

/-- Interchanging the prescribed tuples gives exactly the inverse overlap isomorphism. -/
theorem chartTupleOverlapIso_symm :
    (chartTupleOverlapIso R I d w v).symm = chartTupleOverlapIso R I d v w := rfl

end FLT.Mazur.HilbertChart
