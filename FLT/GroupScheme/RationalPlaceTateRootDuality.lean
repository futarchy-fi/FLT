/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateRealizationRank
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Perfect Cartier duality on the full original C_p Tate realizations -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Finite freeness makes scalar extension commute with the original root dual. -/
def rationalPlaceRootHomBaseChange :
    (ℂ_[p] ⊗[ℤ_[p]] (X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p)) ≃ₗ[ℂ_[p]]
      (RationalPlaceTateRealization X →ₗ[ℂ_[p]] RationalPlaceRootRealization (p := p)) := by
  let : Module.Finite ℤ_[p] X.tateSequences := X.tateSequences_finite
  let : Module.Free ℤ_[p] X.tateSequences := X.tateSequences_free
  exact ((TensorProduct.isBaseChange ℤ_[p] X.tateSequences ℂ_[p]).linearMapLeftRight
    (TensorProduct.isBaseChange ℤ_[p] (TateRootModule (AlgebraicClosure K) p) ℂ_[p])).equiv

/-- Hom base change evaluates the original functional on original unit pure tensors. -/
theorem rationalPlaceRootHomBaseChange_one_tmul
    (f : X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p)
    (x : X.tateSequences) :
    rationalPlaceRootHomBaseChange X (1 ⊗ₜ f) (1 ⊗ₜ x) = 1 ⊗ₜ f x := by
  simp only [rationalPlaceRootHomBaseChange, IsBaseChange.equiv_tmul, one_smul]
  exact IsBaseChange.linearMapLeftRightHom_comp_apply _ _ f x

/-- Perfect Cartier duality after scalar extension, with the genuine cyclotomic root target. -/
def rationalPlaceTateRootDuality : RationalPlaceTateRealization X.cartierDual ≃ₗ[ℂ_[p]]
    (RationalPlaceTateRealization X →ₗ[ℂ_[p]] RationalPlaceRootRealization (p := p)) :=
  (X.tateRootDuality.baseChange ℤ_[p] ℂ_[p] _ _).trans (rationalPlaceRootHomBaseChange X)

/-- The full perfect pairing restricts to the original integral Cartier pairing. -/
theorem rationalPlaceTateRootDuality_one_tmul (y : X.CartierTate) (x : X.tateSequences) :
    rationalPlaceTateRootDuality X (1 ⊗ₜ y) (1 ⊗ₜ x) = 1 ⊗ₜ X.tateRootDuality y x := by
  change rationalPlaceRootHomBaseChange X
    (X.tateRootDuality.baseChange ℤ_[p] ℂ_[p] _ _ (1 ⊗ₜ y)) (1 ⊗ₜ x) = _
  rw [LinearEquiv.baseChange_tmul, rationalPlaceRootHomBaseChange_one_tmul]
end ThreeAdicPlan
