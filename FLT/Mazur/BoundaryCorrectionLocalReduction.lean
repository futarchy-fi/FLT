/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFiniteReduction
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Canonical flat ambient algebras for finite boundary reductions

At an original scalar prime use its actual localization, with its maximal
ideal as the test and reduction ideal. Flatness and contraction are proved
by localization, so the geometric input is now just finite full-equation
reduction data in this specified algebra. No Noetherianity is required.
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
  (P : Ideal R) [P.IsPrime]
local notation "S" => Localization.AtPrime P
local notation "J" => IsLocalRing.maximalIdeal S

/-- Canonical local reductions construct an original scalar outside the prime. -/
theorem localReduction_original {κ : Type*} [Fintype κ]
    (e : κ → S ⊗[R] ((∀ i, B i) × ∀ i j, C i j))
    (v : κ → S ⊗[R] (∀ i, A i)) (c : κ → κ → S)
    (hc : ∀ j k, c j k ∈ J)
    (he : ∀ j, e j - (correctionSystem φ p q u).baseChange S (tensorPair S (0, v j)) =
      ∑ k, c j k • e k)
    (z₀ : S ⊗[R] (∀ i, A i)) (b : κ → S)
    (h₀ : (correctionSystem φ p q u).baseChange S (tensorPair S (1, z₀)) =
      ∑ j, b j • e j) :
    ∃ y : correctionSolutions φ p q u, y.val.1 ∉ P := by
  let _ : Module.Flat R S := IsLocalization.flat S P.primeCompl
  obtain ⟨y, hy⟩ := finiteReduction_original φ p q u S J e v c hc he z₀ b h₀ J le_rfl
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  exact ⟨y, fun h ↦ hy ((IsLocalization.AtPrime.to_map_mem_maximal_iff S P _).mpr h)⟩

/-- The canonical local construction gives original compatible numerators near the prime. -/
theorem localReduction_numerators {κ : Type*} [Fintype κ]
    (e : κ → S ⊗[R] ((∀ i, B i) × ∀ i j, C i j))
    (v : κ → S ⊗[R] (∀ i, A i)) (c : κ → κ → S)
    (hc : ∀ j k, c j k ∈ J)
    (he : ∀ j, e j - (correctionSystem φ p q u).baseChange S (tensorPair S (0, v j)) =
      ∑ k, c j k • e k)
    (z₀ : S ⊗[R] (∀ i, A i)) (b : κ → S)
    (h₀ : (correctionSystem φ p q u).baseChange S (tensorPair S (1, z₀)) =
      ∑ j, b j • e j) :
    ∃ (a : R) (w : ∀ i, A i), a ∉ P ∧
      (∀ i, φ i (w i) = φ i (algebraMap R (A i) a) * φ i (u i)) ∧
      ∀ i j, p i j (w i) = q i j (w j) := by
  obtain ⟨y, hy⟩ := localReduction_original φ p q u P e v c hc he z₀ b h₀
  obtain ⟨w, hw, hz⟩ := (mem_iff_numerators _ _ _ _ _ _ _).mp
    (correctionMultiplier_mem φ p q u y)
  exact ⟨y.val.1, w, hy, hw, hz⟩

end FLT.Mazur.BoundaryCorrectionIdeal
