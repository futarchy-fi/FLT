/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedPointCompletion
public import FLT.Mazur.PolygonCompleteNodeCompletion

/-!
# The actual complete local node over its original base

The affine comparison and the actual germ comparison identify the completed
local stalk at the specified complete node with the arithmetic xy=q
completion, as algebras over the original power-series ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Original complete-base coefficients in the actual complete node stalk. -/
def completeNodeStalkScalars :
    PowerSeries K →+* (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i) :=
  AffineClosedPointQuotient.stalkScalars U ⟨completeNode K n h i, hx⟩
    (completeAffineScalars K n h U)

/-- Completion at the actual affine node agrees with the actual completed local stalk. -/
def completeNodeGermCompletion :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    AdicCompletion (completeNodeAffineIdeal K n h i U hx)
      Γ(exactVeroneseProj K n h, U) ≃ₐ[PowerSeries K]
        AdicCompletion (IsLocalRing.maximalIdeal
          ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
          ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) :=
  AffineClosedPointQuotient.completionAlgebraEquivalence U ⟨completeNode K n h i, hx⟩
    (completeNode_isClosed K n h i) (completeAffineScalars K n h U)

/-- The actual completed local stalk is the arithmetic xy=q completion over the original base. -/
def completeNodeStalkCompletionAlgEquiv :
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    AdicCompletion (IsLocalRing.maximalIdeal
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) ≃ₐ[PowerSeries K]
        AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
          (ChartRing (PowerSeries.X : PowerSeries K)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact (completeNodeGermCompletion K n h i U hx).symm.trans
    (completeNodeCompletionAlgEquiv K n h i U hx)

/-- The local comparison and the affine comparison agree on every completed affine section. -/
theorem completeNodeStalkCompletionAlgEquiv_germ
    (a : AdicCompletion (completeNodeAffineIdeal K n h i U hx)
      Γ(exactVeroneseProj K n h, U)) :
    completeNodeStalkCompletionAlgEquiv K n h i U hx
        (completeNodeGermCompletion K n h i U hx a) =
      completeNodeCompletionAlgEquiv K n h i U hx a := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact congrArg (completeNodeCompletionAlgEquiv K n h i U hx)
    ((completeNodeGermCompletion K n h i U hx).symm_apply_apply a)

end FLT.Mazur.PolygonInfinitesimalStages
