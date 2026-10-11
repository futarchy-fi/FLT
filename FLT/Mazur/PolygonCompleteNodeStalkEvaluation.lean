/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeStalkCompletion

/-!
# Finite evaluations of the actual completed node stalk

The local comparison agrees at every positive power with the original
arithmetic neighborhood map, after the inverse of the actual germ map.
It also retains the original coefficients independently of the affine open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Coefficients in the local stalk are the germs of the actual structural pullback. -/
theorem completeNodeStalkScalars_apply (s : PowerSeries K) :
    completeNodeStalkScalars K n h i U hx s =
      (exactVeroneseProjToBase K n h).stalkMap (completeNode K n h i)
        ((Spec (.of (PowerSeries K))).presheaf.germ ⊤
          ((exactVeroneseProjToBase K n h) (completeNode K n h i)) trivial
          ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv s)) :=
  AffineChartStalkScalars.germ_appLE (exactVeroneseProjToBase K n h) ⊤ U
    (by simp) (completeNode K n h i) hx ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv s)

/-- The original stalk coefficient map is independent of the chosen affine neighborhood. -/
theorem completeNodeStalkScalars_independent
    (V : (exactVeroneseProj K n h).affineOpens) (hy : completeNode K n h i ∈ V.1) :
    completeNodeStalkScalars K n h i U hx = completeNodeStalkScalars K n h i V hy := by
  ext s
  exact (completeNodeStalkScalars_apply K n h i U hx s).trans
    (completeNodeStalkScalars_apply K n h i V hy s).symm

/-- On the original sections the completed germ map is precisely the original germ. -/
theorem completeNodeGermCompletion_of (a : Γ(exactVeroneseProj K n h, U)) :
    completeNodeGermCompletion K n h i U hx
        (AdicCompletion.of (completeNodeAffineIdeal K n h i U hx) _ a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))) _
          ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a) :=
  AffineClosedPointQuotient.completionAlgebraEquivalence_of U ⟨completeNode K n h i, hx⟩
    (completeNode_isClosed K n h i) (completeAffineScalars K n h U) a

/-- Every finite local evaluation is the original arithmetic neighborhood comparison. -/
theorem completeNodeStalkCompletionAlgEquiv_eval (m : ℕ)
    (a : AdicCompletion (IsLocalRing.maximalIdeal
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))) :
    AdicCompletion.evalₐ (coordinateIdeal (PowerSeries.X : PowerSeries K)) (m + 1)
        (completeNodeStalkCompletionAlgEquiv K n h i U hx a) =
      completeNodeArithmeticNeighborhood K n h i U hx m
        ((AffineClosedPointQuotient.equivalence U ⟨completeNode K n h i, hx⟩
          (completeNode_isClosed K n h i) (m + 1)).symm
            (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal
              ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
                (m + 1) a)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  obtain ⟨b, rfl⟩ := (completeNodeGermCompletion K n h i U hx).surjective a
  rw [completeNodeStalkCompletionAlgEquiv_germ, completeNodeCompletionAlgEquiv_eval]
  congr 1
  exact ((AffineClosedPointQuotient.equivalence U ⟨completeNode K n h i, hx⟩
    (completeNode_isClosed K n h i) (m + 1)).symm_apply_eq.mpr
      (AffineClosedPointQuotient.completionAlgebraEquivalence_eval U
        ⟨completeNode K n h i, hx⟩ (completeNode_isClosed K n h i)
        (completeAffineScalars K n h U) (m + 1) b)).symm

end FLT.Mazur.PolygonInfinitesimalStages
