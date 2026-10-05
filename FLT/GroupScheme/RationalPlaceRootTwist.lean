/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalCyclotomicRootGalois
public import FLT.GroupScheme.RationalPlaceTateRealizationRank
public import FLT.GroupScheme.RationalPlaceTateRealizationGalois
public import FLT.GroupScheme.RationalPlaceHodgeTateLieTwist

/-! # The actual root realization is the standard positive cyclotomic line -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]

/-- Coordinates on the actual root realization, normalized by the prescribed primitive roots. -/
def rationalPlaceRootCoordinate : RationalPlaceRootRealization (p := p) ≃ₗ[ℂ_[p]] ℂ_[p] :=
  ((rationalCyclotomicRootEquiv p).symm.baseChange ℤ_[p] ℂ_[p] _ _).trans
    (TensorProduct.AlgebraTensorModule.rid ℤ_[p] ℂ_[p] ℂ_[p])

/-- The prescribed cyclotomic pure tensor has exactly its given scalar coordinate. -/
theorem rationalPlaceRootCoordinate_vector (c : ℂ_[p]) :
    rationalPlaceRootCoordinate p (c ⊗ₜ rationalCyclotomicRootVector p) = c := by
  rw [← rationalCyclotomicRootEquiv_one]
  simp [rationalPlaceRootCoordinate, LinearEquiv.baseChange_tmul]

/-- Both original Galois actions act on the actual scalar-extended root line. -/
def rationalPlaceRootGalois (σ : PadicGalois p) :
    RationalPlaceRootRealization (p := p) →ₗ[ℤ_[p]] RationalPlaceRootRealization (p := p) :=
  TensorProduct.map (rationalPlaceComplexGaloisPadicLinear σ)
    (tateRootGalois ((rationalPlaceGaloisEquiv p).symm σ))

/-- The root action retains the coefficient and geometric factors. -/
theorem rationalPlaceRootGalois_tmul (σ : PadicGalois p) (c : ℂ_[p])
    (x : TateRootModule (AlgebraicClosure
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) p) :
    rationalPlaceRootGalois p σ (c ⊗ₜ x) = complexGalois p σ c ⊗ₜ
      tateRootGalois ((rationalPlaceGaloisEquiv p).symm σ) x := rfl

/-- On all vectors, the original root action is the standard positive cyclotomic twist. -/
theorem rationalPlaceRootCoordinate_galois (σ : PadicGalois p)
    (v : RationalPlaceRootRealization (p := p)) :
    rationalPlaceRootCoordinate p (rationalPlaceRootGalois p σ v) =
      rationalPlaceCyclotomicScalar σ * complexGalois p σ (rationalPlaceRootCoordinate p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨a, rfl⟩ := (rationalCyclotomicRootEquiv p).surjective x
    rw [rationalPlaceRootGalois_tmul, rationalCyclotomicRootEquiv_galois]
    simp only [rationalPlaceRootCoordinate, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      TensorProduct.AlgebraTensorModule.rid_tmul,
      Algebra.smul_def]
    change algebraMap ℤ_[p] ℂ_[p] (_ * a) * complexGalois p σ c = _
    rw [map_mul]
    have ha : complexGalois p σ (algebraMap ℤ_[p] ℂ_[p] a) =
        algebraMap ℤ_[p] ℂ_[p] a := by
      simpa [Algebra.smul_def, rationalPlaceComplexGaloisPadicLinear] using
        (rationalPlaceComplexGaloisPadicLinear σ).map_smul a 1
    simp only [rationalPlaceCyclotomicScalar, map_mul, ha]
    ring
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]
end ThreeAdicPlan
