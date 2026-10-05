/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseGraphProductComparison
public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Properness detected by the affine-base Chow immersion

The constructed graph modification gives a criterion for properness after
any base change, including passage from a finite coefficient ring to the
original ring. The remaining approximation problem is to descend the closed
immersion property uniformly to a finite coefficient stage.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open FLT.Mazur.Approximation

universe u

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {X T : Scheme.{u}}
  (f : X ⟶ Spec R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Properness after base change is equivalent to the explicitly constructed
Chow immersion becoming closed. The cover and immersion are built from `f`. -/
theorem graph_baseChange_isProper_iff (b : T ⟶ Spec R) :
    IsProper (pullback.snd f b) ↔
      IsClosedImmersion (immersionBaseChange (graphClosureπ f ≫ f)
        (chartData f).projectiveProductProjection (graphClosureToProduct f)
        (graphClosureToProduct_projection f) b) := by
  let _surjective : Surjective (graphClosureπ f) := ⟨graphClosureπ_surjective f⟩
  exact proper_baseChange_iff_closedImmersion f (chartData f).projectiveProductProjection
    (graphClosureπ f) (graphClosureToProduct f) (graphClosureToProduct_projection f) b

end FLT.Mazur.Chow.AffineBase
