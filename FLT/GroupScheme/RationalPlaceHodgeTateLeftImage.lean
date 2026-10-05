/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceLieEvaluationEquiv

/-! # Kernel and image of the original left map in Cartier coordinates

These identify the exact remaining differential-surjectivity problem. They
make no assertion that the connected Hodge–Tate sequence is already exact.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- In the original perfect Lie and Cartier coordinates, the left map is the dual differential. -/
theorem rationalPlaceHodgeTateLeft_factorization :
    rationalPlaceHodgeTateLeft X = (rationalPlaceTateLeftDuality X).symm.toLinearMap.comp
      ((rationalPlaceHodgeTateDlogLinear X).dualMap.comp
        (rationalPlaceLieEvaluationEquiv X).toLinearMap) := by
  rw [rationalPlaceLieEvaluationEquiv_eq]
  rfl

/-- The left kernel consists of Lie functionals annihilating the differential image. -/
theorem rationalPlaceHodgeTateLeft_mem_ker (v : RationalPlaceHodgeTateLeftSource X) :
    v ∈ LinearMap.ker (rationalPlaceHodgeTateLeft X) ↔
      ∀ y, rationalPlaceLieEvaluation X v (rationalPlaceHodgeTateDlogLinear X y) = 0 := by
  rw [rationalPlaceHodgeTateLeft_ker, LinearMap.mem_ker]
  exact LinearMap.ext_iff

set_option maxHeartbeats 800000 in
-- Annihilator comparison unfolds the original two duality identifications.
/-- The left image is the Cartier annihilator of the actual differential kernel. -/
theorem rationalPlaceHodgeTateLeft_mem_range (x : RationalPlaceTateRealization X) :
    x ∈ LinearMap.range (rationalPlaceHodgeTateLeft X) ↔
      ∀ y, rationalPlaceHodgeTateDlogLinear X y = 0 →
        rationalPlaceTateScalarDuality X y x = 0 := by
  have he : x ∈ LinearMap.range (rationalPlaceHodgeTateLeft X) ↔
      rationalPlaceTateLeftDuality X x ∈
        LinearMap.range (rationalPlaceHodgeTateDlogLinear X).dualMap := by
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨rationalPlaceLieEvaluation X v, ?_⟩
      change _ = rationalPlaceTateLeftDuality X
        ((rationalPlaceTateLeftDuality X).symm (rationalPlaceHodgeTateLieTranspose X v))
      rw [LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨f, hf⟩
      obtain ⟨v, rfl⟩ := (rationalPlaceLieEvaluationEquiv X).surjective f
      refine ⟨v, (rationalPlaceTateLeftDuality X).injective ?_⟩
      rw [rationalPlaceHodgeTateLeft_factorization]
      change rationalPlaceTateLeftDuality X
        ((rationalPlaceTateLeftDuality X).symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hf
  rw [he, LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  rfl

/-- Left injectivity is precisely surjectivity of the original Cartier differential. -/
theorem rationalPlaceHodgeTateLeft_injective_iff :
    Function.Injective (rationalPlaceHodgeTateLeft X) ↔
      Function.Surjective (rationalPlaceHodgeTateDlogLinear X) := by
  rw [rationalPlaceHodgeTateLeft_factorization]
  change Function.Injective ((rationalPlaceTateLeftDuality X).symm ∘
    (rationalPlaceHodgeTateDlogLinear X).dualMap ∘ rationalPlaceLieEvaluationEquiv X) ↔ _
  rw [(rationalPlaceTateLeftDuality X).symm.injective.of_comp_iff]
  rw [Function.Injective.of_comp_iff' _ (rationalPlaceLieEvaluationEquiv X).bijective]
  exact LinearMap.dualMap_injective_iff
end ThreeAdicPlan
