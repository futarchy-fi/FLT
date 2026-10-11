/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStalkFirstCotangent
public import FLT.Mazur.PolygonCompleteNodeLocalFiniteness

/-!
# The original first cotangent complex at the actual complete node

The actual affine presentation, localized through the actual germ, computes
the completion of original node H1. No comparison with arithmetic H1 is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual affine conormal differential localized at the actual node. -/
def completeNodeConormalDifferential :=
  AffineClosedPointQuotient.stalkConormalDifferential U ⟨completeNode K n h i, hx⟩
    (completeAffineScalars K n h U) (completeAffineScalars_finitePresentation K n h U)

/-- First cotangent homology of the original actual node stalk is finite. -/
theorem completeNodeH1Cotangent_finite :
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Module.Finite ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (Algebra.H1Cotangent (PowerSeries K)
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing Γ(exactVeroneseProj K n h, U) :=
    Algebra.FiniteType.isNoetherianRing (PowerSeries K) _
  exact AffineClosedPointQuotient.stalkH1Cotangent_finite U ⟨completeNode K n h i, hx⟩
    (completeAffineScalars K n h U) (completeAffineScalars_finitePresentation K n h U)

/-- Completed original node H1 is the kernel of its actual completed conormal differential. -/
def completeNodeH1CotangentCompletionEquiv :
    let X := exactVeroneseProj K n h
    let A := X.presheaf.stalk (completeNode K n h i)
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨completeNode K n h i, hx⟩
    let I := IsLocalRing.maximalIdeal A
    AdicCompletion I (Algebra.H1Cotangent (PowerSeries K) A) ≃ₗ[AdicCompletion I A]
      LinearMap.ker (AdicCompletion.map I (completeNodeConormalDifferential K n h i U hx)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing Γ(exactVeroneseProj K n h, U) :=
    Algebra.FiniteType.isNoetherianRing (PowerSeries K) _
  exact AffineClosedPointQuotient.stalkH1CotangentCompletionEquiv U ⟨completeNode K n h i, hx⟩
    (completeAffineScalars K n h U) (completeAffineScalars_finitePresentation K n h U)
    (IsLocalRing.maximalIdeal
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))

end FLT.Mazur.PolygonInfinitesimalStages
