/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLeft
public import FLT.GroupScheme.RationalPlaceLieTransposeGalois
public import FLT.GroupScheme.RationalPlaceTateRootEquivariance

/-! # Equivariance of the actual left Hodge–Tate map -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original diagonal Galois action on the whole Tate realization is surjective. -/
theorem rationalPlaceTateRealizationGalois_surjective (σ : PadicGalois p) :
    Function.Surjective (rationalPlaceTateRealizationGalois X σ) := by
  intro x
  refine ⟨rationalPlaceTateRealizationGalois X σ⁻¹ x, ?_⟩
  rw [← rationalPlaceTateRealizationGalois_mul, mul_inv_cancel,
    rationalPlaceTateRealizationGalois_one]

/-- The actual left map intertwines the positive Lie twist and the original Tate action. -/
theorem rationalPlaceHodgeTateLeft_galois (σ : PadicGalois p)
    (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateLeft X (rationalPlaceHodgeTateLieTwist X σ v) =
      rationalPlaceTateRealizationGalois X σ (rationalPlaceHodgeTateLeft X v) := by
  apply rationalPlaceTateScalarDuality_separates X
  intro y
  obtain ⟨y, rfl⟩ := rationalPlaceTateRealizationGalois_surjective X.cartierDual σ y
  rw [rationalPlaceHodgeTateLeft_pairing, rationalPlaceTateScalarDuality_galois,
    rationalPlaceHodgeTateLeft_pairing, rationalPlaceHodgeTateLieTranspose_galois]
end ThreeAdicPlan
