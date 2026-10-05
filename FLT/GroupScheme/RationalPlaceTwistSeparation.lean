/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLieTwist
public import FLT.PadicHodgeTheory.ComplexNonzeroTwistVanishing
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Positive cyclotomic vectors vanish in untwisted coefficient tensors -/

@[expose] public noncomputable section
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- A C_p coefficient cannot transform by the positive cyclotomic character unless it is zero. -/
theorem rationalPlaceCyclotomicEigen_eq_zero (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p, complexGalois p σ x = rationalPlaceCyclotomicScalar σ * x) :
    x = 0 := by
  apply complexTwist_fixed_eq_zero p (-1) (by decide) x
  intro σ
  have hn : rationalPlaceCyclotomicScalar σ ≠ 0 :=
    ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).isUnit.map
      (algebraMap ℤ_[p] ℂ_[p])).ne_zero
  have hw : (padicCyclotomicWeight p σ (-1) : ℂ_[p]) =
      (rationalPlaceCyclotomicScalar σ)⁻¹ := by
    change algebraMap (PadicAlgCl p) ℂ_[p]
      (algebraMap ℚ_[p] (PadicAlgCl p)
        (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ (-1 : ℤ))) = _
    rw [← IsScalarTower.algebraMap_apply, map_zpow₀, zpow_neg_one]
    congr 1
  rw [hw, hx, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Original O-linear coordinates commute with the coefficient Galois action. -/
theorem rationalPlaceTensorCoordinate_galois {M : Type*} [AddCommGroup M] [Module O M]
    (f : Module.Dual O M) (σ : PadicGalois p) (v : ℂ_[p] ⊗[O] M) :
    f.baseChange ℂ_[p] ((rationalPlaceComplexGalois σ).toLinearMap.rTensor M v) =
      complexGalois p σ (f.baseChange ℂ_[p] v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c m =>
    simp only [LinearMap.rTensor_tmul, Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
    change algebraMap O ℂ_[p] (f m) * complexGalois p σ c = _
    rw [map_mul, rationalPlaceComplexGalois_base]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- No nonzero vector in an untwisted free coefficient tensor has cyclotomic weight one. -/
theorem rationalPlaceTensorCyclotomicEigen_eq_zero {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Free O M] (v : ℂ_[p] ⊗[O] M)
    (hv : ∀ σ : PadicGalois p,
      (rationalPlaceComplexGalois σ).toLinearMap.rTensor M v =
        rationalPlaceCyclotomicScalar σ • v) : v = 0 := by
  let b := Module.Free.chooseBasis O M
  have hz (f : Module.Dual O M) : f.baseChange ℂ_[p] v = 0 := by
    apply rationalPlaceCyclotomicEigen_eq_zero
    intro σ
    rw [← rationalPlaceTensorCoordinate_galois, hv, map_smul, smul_eq_mul]
  apply (b.baseChange ℂ_[p]).repr.injective
  apply Finsupp.ext
  intro i
  have he (w : ℂ_[p] ⊗[O] M) :
      (b.baseChange ℂ_[p]).repr w i = Module.Dual.baseChange ℂ_[p] (b.coord i) w := by
    induction w using TensorProduct.inductionOn with
    | tmul c m => exact b.baseChange_repr_tmul ℂ_[p] c m i
    | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw]
  rw [he, hz, map_zero, Finsupp.zero_apply]
end ThreeAdicPlan
