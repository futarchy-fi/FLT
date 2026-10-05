/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLieTranspose
public import FLT.GroupScheme.RationalPlaceCoefficientGalois
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # The original Lie source with its positive cyclotomic twist

This constructs the source and its action. An injection from this source into
the original Tate realization is not supplied by defining the twist.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The actual positive cyclotomic character in C_p. -/
def rationalPlaceCyclotomicScalar (σ : PadicGalois p) : ℂ_[p] :=
  algebraMap ℤ_[p] ℂ_[p] (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val

/-- The cyclotomic coefficient is fixed by the coefficient Galois action. -/
theorem rationalPlaceCyclotomicScalar_fixed (σ τ : PadicGalois p) :
    complexGalois p σ (rationalPlaceCyclotomicScalar τ) = rationalPlaceCyclotomicScalar τ :=
  complexGalois_algebraMap p σ _

/-- The actual character has positive weight one and obeys multiplication. -/
theorem rationalPlaceCyclotomicScalar_mul (σ τ : PadicGalois p) :
    rationalPlaceCyclotomicScalar (σ * τ) =
      rationalPlaceCyclotomicScalar σ * rationalPlaceCyclotomicScalar τ := by
  change algebraMap ℤ_[p] ℂ_[p]
    ((cyclotomicCharacter (PadicAlgCl p) p) (σ.toRingEquiv * τ.toRingEquiv)).val = _
  rw [map_mul, Units.val_mul, map_mul]
  rfl

/-- The identity Galois element has cyclotomic coefficient one. -/
theorem rationalPlaceCyclotomicScalar_one :
    rationalPlaceCyclotomicScalar (1 : PadicGalois p) = 1 := by
  change algebraMap ℤ_[p] ℂ_[p] ((cyclotomicCharacter (PadicAlgCl p) p) 1).val = 1
  rw [map_one, Units.val_one, map_one]

variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The underlying vector space of Lie(G) tensor C_p(1), using the original Lie module. -/
abbrev RationalPlaceHodgeTateLeftSource := ℂ_[p] ⊗[O] X.IntegralTangent

/-- Galois acts on coefficients and multiplies by the positive cyclotomic character. -/
def rationalPlaceHodgeTateLieTwist (σ : PadicGalois p) :
    RationalPlaceHodgeTateLeftSource X →ₗ[O] RationalPlaceHodgeTateLeftSource X :=
  rationalPlaceCyclotomicScalar σ • (rationalPlaceComplexGalois σ).toLinearMap.rTensor _

/-- The source action exhibits exactly the required positive cyclotomic factor. -/
theorem rationalPlaceHodgeTateLieTwist_tmul (σ : PadicGalois p)
    (c : ℂ_[p]) (d : X.IntegralTangent) :
    rationalPlaceHodgeTateLieTwist X σ (c ⊗ₜ d) =
      (rationalPlaceCyclotomicScalar σ * complexGalois p σ c) ⊗ₜ[O] d := rfl

/-- The identity acts identically on the twisted Lie source. -/
theorem rationalPlaceHodgeTateLieTwist_one (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateLieTwist X 1 v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul c d =>
    simp only [rationalPlaceHodgeTateLieTwist_tmul, rationalPlaceCyclotomicScalar_one,
      complexGalois_one, RingHom.id_apply, one_mul]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The positive twist respects the original Galois group law on the whole Lie source. -/
theorem rationalPlaceHodgeTateLieTwist_mul (σ τ : PadicGalois p)
    (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateLieTwist X (σ * τ) v =
      rationalPlaceHodgeTateLieTwist X σ (rationalPlaceHodgeTateLieTwist X τ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c d =>
    simp only [rationalPlaceHodgeTateLieTwist_tmul, rationalPlaceCyclotomicScalar_mul,
      complexGalois_mul, RingHom.comp_apply, map_mul, rationalPlaceCyclotomicScalar_fixed,
      mul_assoc]
  | add v w hv hw => simp only [map_add, hv, hw]
/-- The positive twist is semilinear for the actual coefficient automorphism. -/
theorem rationalPlaceHodgeTateLieTwist_smul (σ : PadicGalois p)
    (c : ℂ_[p]) (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateLieTwist X σ (c • v) =
      complexGalois p σ c • rationalPlaceHodgeTateLieTwist X σ v := by
  induction v using TensorProduct.inductionOn with
  | tmul b d =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul,
      rationalPlaceHodgeTateLieTwist_tmul, map_mul]
    congr 1
    ring
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
end ThreeAdicPlan
