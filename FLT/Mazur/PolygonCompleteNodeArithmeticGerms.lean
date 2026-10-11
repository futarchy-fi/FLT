/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeArithmeticAction
public import FLT.Mazur.PolygonCompleteNodeStalkEvaluation

/-!
# Original germs in the faithfully flat arithmetic node model

The actual local-ring action on the arithmetic completion extends the same
original affine comparison, at every positive finite evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual arithmetic local action agrees with the completed affine comparison on germs. -/
theorem completeNodeArithmeticScalars_germ (a : Γ(exactVeroneseProj K n h, U)) :
    completeNodeArithmeticScalars K n h i U hx
        ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a) =
      completeNodeCompletionAlgEquiv K n h i U hx
        (AdicCompletion.of (completeNodeAffineIdeal K n h i U hx) _ a) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact (congrArg (completeNodeStalkCompletionAlgEquiv K n h i U hx)
    (completeNodeGermCompletion_of K n h i U hx a).symm).trans
      (completeNodeStalkCompletionAlgEquiv_germ K n h i U hx _)

/-- At every positive order the actual local action is the original neighborhood comparison. -/
theorem completeNodeArithmeticScalars_germ_eval (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U)) :
    AdicCompletion.evalₐ (coordinateIdeal (PowerSeries.X : PowerSeries K)) (m + 1)
      (completeNodeArithmeticScalars K n h i U hx
        ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a)) =
      completeNodeArithmeticNeighborhood K n h i U hx m (Ideal.Quotient.mk _ a) := by
  rw [completeNodeArithmeticScalars_germ, completeNodeCompletionAlgEquiv_eval,
    AdicCompletion.evalₐ_of]

end FLT.Mazur.PolygonInfinitesimalStages
