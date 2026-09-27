/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralEtaleAlgebra
public import FLT.GroupScheme.IntegralHopfAlgebra

/-!
# Integral étale models away from ramification

For a finite continuous Galois module unramified outside a finite set `S` of primes,
the normalization of `ℤ[1/S]` in its generic coordinate algebra is a finite étale,
commutative and cocommutative Hopf algebra. Its base change to `ℚ` is identified
with the given generic coordinate algebra as a bialgebra.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

namespace FiniteContinuousGaloisModule

/-- The finite étale commutative group scheme over `ℤ[1/S]` attached to a finite
continuous Galois module unramified outside `S`. Its generic fibre is the canonical
equivariant-function bialgebra. -/
def integralEtaleModel (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)]
    (W : FiniteContinuousGaloisModule) (h : UnramifiedOutside S W) :
    FiniteEtaleModel (ZInvPrimes S) W := by
  let R := ZInvPrimes S
  let A := W.GenericCoordinateAlgebra
  let H := W.IntegralCoordinateAlgebra S
  letI : Algebra.Etale R H := W.integralCoordinateAlgebraEtale S h
  letI : HopfAlgebra R H := integralClosureHopfAlgebra R ℚ A
  letI : Coalgebra.IsCocomm R H := integralClosureCocomm R ℚ A
  letI : HopfAlgebra.IsFiniteFlat R H := ⟨⟩
  exact { toHasFiniteFlatModel := HasFiniteFlatModel.ofGenericBialgEquiv W H
            (integralGenericBialgEquiv R ℚ A)
          etale := by change Algebra.Etale R H; infer_instance }

/-- The generic fibre of the integral étale model is the prescribed bialgebra. -/
def integralEtaleModelGenericEquiv (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)]
    (W : FiniteContinuousGaloisModule) (h : UnramifiedOutside S W) :
    ℚ ⊗[ZInvPrimes S] (W.integralEtaleModel S h).CoordinateRing ≃ₐc[ℚ]
      W.GenericCoordinateAlgebra :=
  (W.integralEtaleModel S h).toHasFiniteFlatModel.genericBialgEquiv.symm

end FiniteContinuousGaloisModule
end ThreeAdicPlan
