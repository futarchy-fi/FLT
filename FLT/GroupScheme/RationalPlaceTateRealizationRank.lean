/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateRootRank
public import FLT.GroupScheme.RationalPlaceHodgeTateRealization

/-! # Dimensions of the original C_p Tate realizations and actual root line -/

@[expose] public noncomputable section
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

/-- The whole original Tate realization is finite dimensional over C_p. -/
theorem rationalPlace_tateRealization_finite :
    Module.Finite ℂ_[p] (RationalPlaceTateRealization X) := by
  let : Module.Finite ℤ_[p] X.tateSequences := X.tateSequences_finite
  exact Module.Finite.base_change ℤ_[p] ℂ_[p] X.tateSequences

/-- The original Tate realization has dimension exactly the integral system height. -/
theorem rationalPlace_tateRealization_finrank :
    Module.finrank ℂ_[p] (RationalPlaceTateRealization X) = height := by
  let : Module.Free ℤ_[p] X.tateSequences := X.tateSequences_free
  change Module.finrank ℂ_[p] (ℂ_[p] ⊗[ℤ_[p]] X.tateSequences) = height
  rw [Module.finrank_baseChange, X.tateSequences_finrank]

/-- The dual realization has the same proved dimension, without assuming comparison exactness. -/
theorem rationalPlace_cartierTateRealization_finrank :
    Module.finrank ℂ_[p] (RationalPlaceTateRealization X.cartierDual) = height :=
  rationalPlace_tateRealization_finrank X.cartierDual

/-- C_p scalar extension of the actual coherent-root module. -/
abbrev RationalPlaceRootRealization := ℂ_[p] ⊗[ℤ_[p]] TateRootModule (AlgebraicClosure K) p

variable (p) (hp : 2 < p)
include hp

/-- The genuine root realization is finite dimensional. -/
theorem rationalPlace_rootRealization_finite :
    Module.Finite ℂ_[p] (RationalPlaceRootRealization (p := p)) := by
  let : Module.Finite ℤ_[p] (TateRootModule (AlgebraicClosure K) p) :=
    rationalPlace_tateRoot_finite p hp
  exact Module.Finite.base_change ℤ_[p] ℂ_[p] _

/-- The genuine C_p root realization has dimension one. -/
theorem rationalPlace_rootRealization_finrank :
    Module.finrank ℂ_[p] (RationalPlaceRootRealization (p := p)) = 1 := by
  let : Module.Free ℤ_[p] (TateRootModule (AlgebraicClosure K) p) :=
    rationalPlace_tateRoot_free p hp
  change Module.finrank ℂ_[p] (ℂ_[p] ⊗[ℤ_[p]] TateRootModule (AlgebraicClosure K) p) = 1
  rw [Module.finrank_baseChange, rationalPlace_tateRoot_finrank p hp]
end ThreeAdicPlan
