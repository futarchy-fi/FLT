/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionAdicAmbient
public import FLT.Mazur.FiniteReductionKernelPairs

/-!
# Full ambient corrections from finite reduction matrices

The error frame lives in the full boundary and independent mixed equation
module. Its finite reduction matrix constructs a uniform error module and all
approximation orders, as well as an exact correction over any ambient algebra.
Flatness is needed only for descent; Noetherianity is not required.
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
  (J : Ideal S) {κ : Type*} [Fintype κ]
  (e : κ → S ⊗[R] ((∀ i, B i) × ∀ i j, C i j))
  (v : κ → S ⊗[R] (∀ i, A i)) (c : κ → κ → S)
  (hc : ∀ j k, c j k ∈ J)
  (he : ∀ j, e j - (correctionSystem φ p q u).baseChange S (tensorPair S (0, v j)) =
    ∑ k, c j k • e k)
  (z₀ : S ⊗[R] (∀ i, A i)) (b : κ → S)
  (h₀ : (correctionSystem φ p q u).baseChange S (tensorPair S (1, z₀)) =
    ∑ j, b j • e j)
include hc he h₀

/-- Finite full-equation data construct the uniform error module and all approximation orders. -/
theorem finiteReduction_approximations :
    ∃ E : Submodule S (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)), E.FG ∧
      ∀ n : ℕ, ∃ z : S ⊗[R] (∀ i, A i),
        (correctionSystem φ p q u).baseChange S (tensorPair S (1, z)) ∈ J ^ n • E :=
  FiniteErrorReduction.exists_kernel_approximations
    (((correctionSystem φ p q u).baseChange S).comp (tensorPair S)) J e v c hc he z₀ b h₀

/-- A finite reduction matrix constructs an exact full ambient correction with scalar near one. -/
theorem finiteReduction_ambient :
    ∃ x : S ⊗[R] (R × ∀ i, A i),
      (correctionSystem φ p q u).lTensor S x = 0 ∧
        tensorCorrectionMultiplier (A := A) S x - 1 ∈ J := by
  obtain ⟨a, z, ha, hz⟩ := FiniteErrorReduction.exists_kernel_pair
    (((correctionSystem φ p q u).baseChange S).comp (tensorPair S)) J e v c hc he z₀ b h₀
  exact ⟨tensorPair S (a, z), hz, by rwa [tensorPair_correctionMultiplier]⟩

variable [Module.Flat R S]

/-- Flat descent gives an original simultaneous correction nonvanishing over the test ideal. -/
theorem finiteReduction_original (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ y : correctionSolutions φ p q u, algebraMap R S y.val.1 ∉ P := by
  obtain ⟨x, hx, hs⟩ := finiteReduction_ambient φ p q u S J e v c hc he z₀ b h₀
  exact flatCorrection_exists_nonvanishing_solution φ p q u S P x hx
    (multiplier_not_mem J P hJP hP hs)

/-- The descended shared correction supplies actual original compatible numerators. -/
theorem finiteReduction_numerators (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ (a : R) (w : ∀ i, A i), algebraMap R S a ∉ P ∧
      (∀ i, φ i (w i) = φ i (algebraMap R (A i) a) * φ i (u i)) ∧
      ∀ i j, p i j (w i) = q i j (w j) := by
  obtain ⟨y, hy⟩ := finiteReduction_original φ p q u S J e v c hc he z₀ b h₀ P hJP hP
  obtain ⟨w, hw, hz⟩ := (mem_iff_numerators _ _ _ _ _ _ _).mp
    (correctionMultiplier_mem φ p q u y)
  exact ⟨y.val.1, w, hy, hw, hz⟩

end FLT.Mazur.BoundaryCorrectionIdeal
