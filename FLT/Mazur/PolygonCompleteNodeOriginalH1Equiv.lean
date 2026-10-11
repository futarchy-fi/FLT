/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedFirstCotangentEquiv
public import FLT.Mazur.PolygonCompleteNodeOriginalSpaceMap

/-!
# Completed original H1 for the actual node and the arithmetic node

The formal node comparison now identifies completions of the ORIGINAL
first cotangent homology modules. Both infinitesimal lifts and their
inverse identities on original cycles are constructed, not assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] AdicInfinitesimalKernelEquiv.forwardInverse
  AdicInfinitesimalKernelEquiv.reverseInverse

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual affine node and xy=q have equivalent completed original first cotangent homology. -/
def completeNodeOriginalH1Equiv :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let e := completeNodeCompletionAlgEquiv K n h i U hx
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      (AdicCompletion (completeNodeAffineIdeal K n h i U hx)
        (Algebra.H1Cotangent (PowerSeries K) Γ(exactVeroneseProj K n h, U)))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (Algebra.H1Cotangent (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing Γ(exactVeroneseProj K n h, U) :=
    Algebra.FiniteType.isNoetherianRing (PowerSeries K) _
  let P := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
  let Q := chartGenerators (PowerSeries.X : PowerSeries K)
  let _ : IsNoetherianRing P.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  let _ : IsNoetherianRing Q.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  let _ := arithmeticNodeIdeal_isMaximal K
  exact AdicCompletedFirstCotangentEquiv.equiv P Q
    (completeNodeAffineIdeal K n h i U hx)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCompletionAlgEquiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
