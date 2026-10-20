/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProductAdicIdeals
public import FLT.Mazur.BoundaryCorrectionOperatorIndependence

/-!
# One exact ideal for all boundary and mixed errors

The equation ideal retains every coordinate of the original correction
operator. Its powers are exactly the coordinate powers at one common order.
Representatives of a full reduced solution therefore give an actual original
error in this ideal power, without any finiteness assumption on scalar modules.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (K : ∀ i, Ideal (B i)) (L : ∀ i j, Ideal (C i j))

/-- A single ideal of the complete original boundary-and-mixed equation ring. -/
def fullEquationIdeal : Ideal ((∀ i, B i) × ∀ i j, C i j) :=
  (Ideal.pi K).prod (Ideal.pi fun i ↦ Ideal.pi (L i))

/-- Exact power membership retains every boundary and independent mixed coordinate. -/
theorem mem_fullEquationIdeal_pow (n : ℕ) (x : (∀ i, B i) × ∀ i j, C i j) :
    x ∈ fullEquationIdeal K L ^ n ↔
      (∀ i, x.1 i ∈ K i ^ n) ∧ ∀ i j, x.2 i j ∈ L i j ^ n := by
  rw [fullEquationIdeal, FiniteProductAdicIdeals.prod_pow, Ideal.mem_prod,
    FiniteProductAdicIdeals.mem_pi_pow, FiniteProductAdicIdeals.mem_pi_pow]
  simp only [FiniteProductAdicIdeals.mem_pi_pow]

/-- The exact original equation error is controlled by its full coordinate errors. -/
theorem original_error_mem_fullEquationIdeal (n : ℕ) (t : ∀ i, B i) (w : ∀ i, A i)
    (hb : ∀ i, t i - φ i (w i) ∈ K i ^ n)
    (hm : ∀ i j, p i j (w i) - q i j (w j) ∈ L i j ^ n) :
    (t, 0) - originalCorrectionOperator φ p q 0 w ∈ fullEquationIdeal K L ^ n := by
  rw [mem_fullEquationIdeal_pow, originalCorrectionOperator_apply]
  refine ⟨hb, fun i j ↦ ?_⟩
  change 0 - (p i j (w i) - q i j (w j)) ∈ L i j ^ n
  simpa only [zero_sub] using (L i j ^ n).neg_mem (hm i j)

variable {A' B' : ι → Type*} {C' : ι → ι → Type*}
  [∀ i, CommRing (A' i)] [∀ i, CommRing (B' i)] [∀ i j, CommRing (C' i j)]
  (r : ∀ i, A i →+* A' i) (s : ∀ i, B i →+* B' i)
  (u : ∀ i j, C i j →+* C' i j)
  (φ' : ∀ i, A' i →+* B' i)
  (p' : ∀ i j, A' i →+* C' i j) (q' : ∀ i j, A' j →+* C' i j)

/-- Actual representatives of a full reduced solution produce the coupled original error. -/
theorem reduced_representatives_full_error (n : ℕ)
    (hs : ∀ i, RingHom.ker (s i) = K i ^ n)
    (hu : ∀ i j, RingHom.ker (u i j) = L i j ^ n)
    (hφ : ∀ i x, s i (φ i x) = φ' i (r i x))
    (hp : ∀ i j x, u i j (p i j x) = p' i j (r i x))
    (hq : ∀ i j x, u i j (q i j x) = q' i j (r j x))
    (t : ∀ i, B i) (v : ∀ i, A' i) (w : ∀ i, A i)
    (hw : ∀ i, r i (w i) = v i)
    (hb : ∀ i, s i (t i) = φ' i (v i))
    (hm : ∀ i j, p' i j (v i) = q' i j (v j)) :
    (t, 0) - originalCorrectionOperator φ p q 0 w ∈ fullEquationIdeal K L ^ n := by
  apply original_error_mem_fullEquationIdeal φ p q K L n t w
  · intro i
    rw [← hs]
    change s i (t i - φ i (w i)) = 0
    rw [map_sub, hφ, hw, hb, sub_self]
  · intro i j
    rw [← hu]
    change u i j (p i j (w i) - q i j (w j)) = 0
    rw [map_sub, hp, hq, hw, hw, hm, sub_self]

/-- Surjectivity of the actual source reductions constructs a full original error vector. -/
theorem exists_full_error_of_reduced_solution (n : ℕ)
    (hr : ∀ i, Function.Surjective (r i))
    (hs : ∀ i, RingHom.ker (s i) = K i ^ n)
    (hu : ∀ i j, RingHom.ker (u i j) = L i j ^ n)
    (hφ : ∀ i x, s i (φ i x) = φ' i (r i x))
    (hp : ∀ i j x, u i j (p i j x) = p' i j (r i x))
    (hq : ∀ i j x, u i j (q i j x) = q' i j (r j x))
    (t : ∀ i, B i) (v : ∀ i, A' i)
    (hb : ∀ i, s i (t i) = φ' i (v i))
    (hm : ∀ i j, p' i j (v i) = q' i j (v j)) :
    ∃ w : ∀ i, A i,
      (t, 0) - originalCorrectionOperator φ p q 0 w ∈ fullEquationIdeal K L ^ n := by
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice fun i ↦ hr i (v i)
  exact ⟨w, reduced_representatives_full_error φ p q K L r s u φ' p' q'
    n hs hu hφ hp hq t v w hw hb hm⟩

end FLT.Mazur.BoundaryCorrectionIdeal
