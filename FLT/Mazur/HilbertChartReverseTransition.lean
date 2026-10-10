/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisTupleSchemeComparison

/-!
# Factoring chart transitions into the reverse overlap

The universal family on the first chart has its first tuple as a basis
everywhere. The scheme comparison therefore factors its change of tuple
through the reverse transition domain, and changing back recovers inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- Cache coefficients for universal chart inference. -/
local instance reverseCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the universal source chart ring. -/
local instance reverseSourceRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the universal target chart ring. -/
local instance reverseTargetRing : CommRing (ChartRing R I d v) := inferInstance

/-- The first tuple remains a basis on every transition domain in its chart. -/
def chartTupleSelfFactor : (chartTupleTransitionOpen R I d w v).toScheme ⟶
    (chartTupleTransitionOpen R I d w w).toScheme :=
  (Spec (.of (ChartRing R I d w))).homOfLE
    (by rw [chartTupleTransitionOpen_self]; exact le_top)

/-- Both universal-family tests have the same map to the first chart. -/
theorem chartTupleSelfFactor_over :
    (𝟙 (chartTupleTransitionOpen R I d w v).toScheme) ≫
      (chartTupleTransitionOpen R I d w v).ι =
    chartTupleSelfFactor R I d w v ≫ (chartTupleTransitionOpen R I d w w).ι := by
  rw [Category.id_comp, chartTupleSelfFactor, Scheme.homOfLE_ι]

/-- The actual transition factors into the reverse overlap domain. -/
def chartTupleReverseMorphism : (chartTupleTransitionOpen R I d w v).toScheme ⟶
    (chartTupleTransitionOpen R I d v w).toScheme :=
  intrinsicTupleComparison R I d v w (ChartRing R I d w) (chartIdentityIdeal R I d w)
    (𝟙 _) (chartTupleSelfFactor R I d w v) (chartTupleSelfFactor_over R I d w v)

/-- The reverse-domain factorization is the original change-of-tuple map. -/
theorem chartTupleReverseMorphism_ι :
    chartTupleReverseMorphism R I d w v ≫ (chartTupleTransitionOpen R I d v w).ι =
      chartTupleTransition R I d w v := by
  rw [chartTupleReverseMorphism, intrinsicTupleComparison_ι, Category.id_comp]
  rfl

/-- Changing back after the factorized transition recovers the original chart inclusion. -/
theorem chartTupleReverseMorphism_transition :
    chartTupleReverseMorphism R I d w v ≫ chartTupleTransition R I d v w =
      (chartTupleTransitionOpen R I d w v).ι := by
  rw [chartTupleReverseMorphism, intrinsicTupleComparison_transition]
  change chartTupleSelfFactor R I d w v ≫ chartTupleTransition R I d w w = _
  rw [chartTupleTransition_self, chartTupleSelfFactor, Scheme.homOfLE_ι]

end FLT.Mazur.HilbertChart
