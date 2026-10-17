/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionLocalReduction
public import FLT.Mazur.FiniteCokernelKernelPairs

/-!
# Constructing ambient boundary corrections from finite cokernel data

The cokernel keeps the entire boundary and every independent mixed equation.
Its finite divisible submodule constructs all matrix data required for flat
descent. Localizations at original scalar primes are the canonical ambient
algebras; no global test map from a completion to the source is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
open FiniteErrorLinearLifting
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The correction-only map retains every full equation after scalar extension. -/
def ambientCorrectionOperator :
    (S ⊗[R] (∀ i, A i)) →ₗ[S] (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) :=
  (((correctionSystem φ p q u).baseChange S).comp (tensorPair S)).comp
    (LinearMap.inr S S (S ⊗[R] (∀ i, A i)))

/-- The scalar-one obstruction in the full ambient target. -/
def ambientScalarError : S ⊗[R] ((∀ i, B i) × ∀ i j, C i j) :=
  (correctionSystem φ p q u).baseChange S (tensorPair S (1, 0))

set_option quotPrecheck false
local notation "F" => ambientCorrectionOperator φ p q u S
local notation "π" => (LinearMap.range F).mkQ
variable (J : Ideal S)

/-- Finite cokernel data construct an exact full ambient correction. -/
theorem finiteCokernel_ambient
    (Q : Submodule S ((S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range F))
    (hQ : Q.FG) (hred : Q ≤ J • Q)
    (hseed : π (ambientScalarError φ p q u S) ∈ Q) :
    ∃ x : S ⊗[R] (R × ∀ i, A i),
      (correctionSystem φ p q u).lTensor S x = 0 ∧
        tensorCorrectionMultiplier (A := A) S x - 1 ∈ J := by
  obtain ⟨a, z, ha, hz⟩ := FiniteErrorReduction.exists_kernel_pair_of_cokernel
    (((correctionSystem φ p q u).baseChange S).comp (tensorPair S)) J Q hQ hred hseed
  exact ⟨tensorPair S (a, z), hz, by rwa [tensorPair_correctionMultiplier]⟩

/-- Flat descent constructs an original nonvanishing solution from the finite cokernel. -/
theorem finiteCokernel_original [Module.Flat R S]
    (Q : Submodule S ((S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range F))
    (hQ : Q.FG) (hred : Q ≤ J • Q)
    (hseed : π (ambientScalarError φ p q u S) ∈ Q)
    (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ y : correctionSolutions φ p q u, algebraMap R S y.val.1 ∉ P := by
  obtain ⟨x, hx, hs⟩ := finiteCokernel_ambient φ p q u S J Q hQ hred hseed
  exact flatCorrection_exists_nonvanishing_solution φ p q u S P x hx
    (multiplier_not_mem J P hJP hP hs)

end FLT.Mazur.BoundaryCorrectionIdeal
