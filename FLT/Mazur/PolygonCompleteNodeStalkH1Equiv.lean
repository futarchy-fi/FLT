/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeGermH1Equiv
public import FLT.Mazur.PolygonCompleteNodeOriginalH1Equiv

/-!
# Completed original stalk H1 and the arithmetic node

The actual germ localization and the constructed affine presentation
comparison identify completed ORIGINAL stalk H1 with arithmetic H1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeGermH1Equiv completeNodeOriginalH1Equiv
attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual completed stalk H1 is arithmetic H1 over the original-base node comparison. -/
def completeNodeStalkH1Equiv :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let e := completeNodeStalkCompletionAlgEquiv K n h i U hx
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      (AdicCompletion (IsLocalRing.maximalIdeal L) (Algebra.H1Cotangent (PowerSeries K) L))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (Algebra.H1Cotangent (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ : RingHomCompTriple
      (completeNodeGermCompletion K n h i U hx).symm.toRingHom
      (completeNodeCompletionAlgEquiv K n h i U hx).toRingHom
      (completeNodeStalkCompletionAlgEquiv K n h i U hx).toRingHom := ⟨rfl⟩
  let _ : RingHomCompTriple
      (completeNodeCompletionAlgEquiv K n h i U hx).symm.toRingHom
      (completeNodeGermCompletion K n h i U hx).toRingHom
      (completeNodeStalkCompletionAlgEquiv K n h i U hx).symm.toRingHom := ⟨rfl⟩
  exact (completeNodeGermH1Equiv K n h i U hx).symm.trans
    (completeNodeOriginalH1Equiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
