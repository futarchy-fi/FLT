/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartOverlapIso

/-!
# Transitions on actual triple intersections of Hilbert charts

Compare the second and third tuple parameters of the first universal family
on the actual pullback of their basis opens. The comparison constructs the
map needed for scheme gluing and computes both of its projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v z : Fin d → MvPolynomial I R)

/-- Cache coefficients for universal-family comparison. -/
local instance tripleCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the first chart ring. -/
local instance tripleSourceRing : CommRing (ChartRing R I d w) := inferInstance

/-- The comparison of the second and third parameters on their actual common domain. -/
def chartTupleTripleComparison :
    pullback (chartTupleTransitionOpen R I d w v).ι (chartTupleTransitionOpen R I d w z).ι ⟶
      (chartTupleTransitionOpen R I d v z).toScheme :=
  intrinsicTupleComparison R I d v z (ChartRing R I d w) (chartIdentityIdeal R I d w)
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- The triple comparison maps to the second chart by the first transition. -/
@[reassoc]
theorem chartTupleTripleComparison_ι :
    chartTupleTripleComparison R I d w v z ≫ (chartTupleTransitionOpen R I d v z).ι =
      pullback.fst _ _ ≫ chartTupleTransition R I d w v :=
  intrinsicTupleComparison_ι R I d v z (ChartRing R I d w) (chartIdentityIdeal R I d w) _ _ _

/-- On the triple domain, successive chart transitions recover the direct third parameter. -/
@[reassoc]
theorem chartTupleTripleComparison_transition :
    chartTupleTripleComparison R I d w v z ≫ chartTupleTransition R I d v z =
      pullback.snd _ _ ≫ chartTupleTransition R I d w z :=
  intrinsicTupleComparison_transition R I d v z (ChartRing R I d w)
    (chartIdentityIdeal R I d w) _ _ _

/-- The actual cyclic map between the triple pullbacks used in scheme gluing. -/
def chartTupleTripleMap :
    pullback (chartTupleTransitionOpen R I d w v).ι (chartTupleTransitionOpen R I d w z).ι ⟶
    pullback (chartTupleTransitionOpen R I d v z).ι (chartTupleTransitionOpen R I d v w).ι :=
  pullback.lift (chartTupleTripleComparison R I d w v z)
    (pullback.fst _ _ ≫ chartTupleReverseMorphism R I d w v) (by
      rw [Category.assoc, chartTupleReverseMorphism_ι, chartTupleTripleComparison_ι])

/-- The first projection of the cyclic triple map is the actual tuple comparison. -/
@[reassoc]
theorem chartTupleTripleMap_fst :
    chartTupleTripleMap R I d w v z ≫ pullback.fst _ _ =
      chartTupleTripleComparison R I d w v z :=
  pullback.lift_fst _ _ _

/-- The second projection is the factorized first chart transition. -/
@[reassoc]
theorem chartTupleTripleMap_snd :
    chartTupleTripleMap R I d w v z ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ chartTupleReverseMorphism R I d w v :=
  pullback.lift_snd _ _ _

end FLT.Mazur.HilbertChart
