/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeAffineIdeal

/-!
# The actual complete node neighborhoods on their original stages

The chosen maximal ideal, its actual parameter membership, and its exact
image ideal specialize the affine neighborhood construction to a specified
node. Every original coefficient and section restriction is retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageNeighborhoodQuotient

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (i : Fin n) (U : (exactVeroneseProj K n h).affineOpens)
  (hx : completeNode K n h i ∈ U.1)

/-- The chosen complete node neighborhood is its actual original-stage point neighborhood. -/
def completeNodeNeighborhood (m : ℕ) :
    (Γ(exactVeroneseProj K n h, U) ⧸ completeNodeAffineIdeal K n h i U hx ^ (m + 1)) ≃+*
      (Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) ⧸
        originalNodeAffineIdeal K n h i U hx m ^ (m + 1)) :=
  (originalStageNeighborhoodQuotient K n h U m (completeNodeAffineIdeal K n h i U hx)
    (completeNodeAffineIdeal_parameter K n h i U hx)).trans
      (Ideal.quotEquivOfEq (congrArg (fun J ↦ J ^ (m + 1))
        (completeNodeAffineIdeal_map K n h i U hx m)))

/-- The chosen node comparison retains the actual original stage section restriction. -/
@[simp] theorem completeNodeNeighborhood_mk (m : ℕ) (a : Γ(exactVeroneseProj K n h, U)) :
    completeNodeNeighborhood K n h i U hx m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ((originalStageToCompatibleProj K n h m).app U a) := by
  rw [completeNodeNeighborhood, RingEquiv.trans_apply,
    originalStageNeighborhoodQuotient_mk, Ideal.quotEquivOfEq_mk]

/-- The original complete-base coefficients survive at the specified node unchanged. -/
theorem completeNodeNeighborhood_scalar (m : ℕ) (r : PowerSeries K) :
    completeNodeNeighborhood K n h i U hx m
      (Ideal.Quotient.mk _ (completeAffineScalars K n h U r)) =
        Ideal.Quotient.mk _ (originalStageAffineScalars K n h m U r) := by
  rw [completeNodeNeighborhood_mk, originalStage_app_scalars]

end FLT.Mazur.PolygonInfinitesimalStages
