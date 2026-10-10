/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationStages
public import Mathlib.Data.Fintype.Sigma

/-!
# Finite relation witnesses for full polynomial equations

An equality modulo the original ideal is witnessed by the differences on
finitely many polynomial generators. Any stage containing those witnesses
satisfies the equation on the entire source polynomial ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- A full equation between polynomial maps has finitely many relation witnesses. -/
theorem exists_equation_seed {n : ℕ} (f g : MvPolynomial (Fin n) R →ₐ[R] P)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) :
    ∃ s : Finset I, ∀ (t : Finset I), s ≤ t →
      (Ideal.Quotient.mkₐ R (relations I t)).comp f =
        (Ideal.Quotient.mkₐ R (relations I t)).comp g := by
  classical
  have he (i : Fin n) : f (MvPolynomial.X i) - g (MvPolynomial.X i) ∈ I := by
    apply Ideal.Quotient.eq.mp
    exact AlgHom.congr_fun h (MvPolynomial.X i)
  let z (i : Fin n) : I := ⟨f (MvPolynomial.X i) - g (MvPolynomial.X i), he i⟩
  refine ⟨Finset.univ.image z, fun t ht ↦ ?_⟩
  apply MvPolynomial.algHom_ext
  intro i
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span ⟨z i, ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), rfl⟩

variable {ι : Type w} [Finite ι]

/-- Different polynomial sources share a single finite set of equation witnesses. -/
theorem exists_equation_seeds (n : ι → ℕ)
    (f g : ∀ i, MvPolynomial (Fin (n i)) R →ₐ[R] P)
    (h : ∀ i, (Ideal.Quotient.mkₐ R I).comp (f i) =
      (Ideal.Quotient.mkₐ R I).comp (g i)) :
    ∃ s : Finset I, ∀ (t : Finset I), s ≤ t → ∀ i,
      (Ideal.Quotient.mkₐ R (relations I t)).comp (f i) =
        (Ideal.Quotient.mkₐ R (relations I t)).comp (g i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose s hs using fun i ↦ exists_equation_seed I (f i) (g i) (h i)
  refine ⟨Finset.univ.biUnion s, fun t ht i ↦ hs i t (le_trans ?_ ht)⟩
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩

end FLT.Mazur.FiniteRelationModel
