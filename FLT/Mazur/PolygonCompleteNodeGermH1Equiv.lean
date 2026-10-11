/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicLocalizedH1Comparison
public import FLT.Mazur.PolygonCompleteNodeFirstCotangent
public import FLT.Mazur.PolygonCompleteNodeStalkEvaluation

/-!
# Original first cotangent homology through the actual node germ

Localization by the actual germ identifies completed original affine H1
with completed original stalk H1, semilinearly over the same completed germ.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Completed original H1 is preserved by the actual node germ localization. -/
def completeNodeGermH1Equiv :
    let X := exactVeroneseProj K n h
    let L := X.presheaf.stalk (completeNode K n h i)
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let e := completeNodeGermCompletion K n h i U hx
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      (AdicCompletion (completeNodeAffineIdeal K n h i U hx)
        (Algebra.H1Cotangent (PowerSeries K) Γ(X, U)))
      (AdicCompletion (IsLocalRing.maximalIdeal L) (Algebra.H1Cotangent (PowerSeries K) L)) := by
  let X := exactVeroneseProj K n h
  let x : U.1 := ⟨completeNode K n h i, hx⟩
  let L := X.presheaf.stalk x
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ : IsScalarTower (PowerSeries K) Γ(X, U) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ := U.2.isLocalization_stalk x
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing Γ(X, U) :=
    Algebra.FiniteType.isNoetherianRing (PowerSeries K) _
  let _ := AdicPresentationFirstCotangent.h1_finite
    (Algebra.Presentation.ofFinitePresentation (PowerSeries K) Γ(X, U)).toGenerators
  let e := completeNodeGermCompletion K n h i U hx
  let eA : AdicCompletion (completeNodeAffineIdeal K n h i U hx) Γ(X, U) ≃ₐ[Γ(X, U)]
      AdicCompletion (IsLocalRing.maximalIdeal L) L :=
    { e.toRingEquiv with commutes' := fun a ↦ completeNodeGermCompletion_of K n h i U hx a }
  exact AdicLocalizedH1Comparison.equiv (R := PowerSeries K)
    (U.2.primeIdealOf x).asIdeal.primeCompl (completeNodeAffineIdeal K n h i U hx)
    (IsLocalRing.maximalIdeal L) eA

end FLT.Mazur.PolygonInfinitesimalStages
