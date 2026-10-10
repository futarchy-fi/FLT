/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialStableStages
public import FLT.Mazur.FinitePolynomialEquationSeeds

/-!
# Simultaneous relation stages with full diagram equations

Prescribed finite families of equations hold on full polynomial source rings
at the same stage that closes every arrow. Equations are assumed only after
projection to the original rings; their finite-stage witnesses are constructed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E] (n : ι → ℕ) (src dst : E → ι)

/-- Close all arrows and impose all original polynomial path equations at one stage. -/
theorem exists_stable_stages_with_equations
    (f : ∀ e, MvPolynomial (Fin (n (src e))) R →ₐ[R]
      MvPolynomial (Fin (n (dst e))) R)
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ e, I (src e) ≤ (I (dst e)).comap (f e).toRingHom)
    (s : ∀ i, Finset (I i)) (C : ι → Type z) [∀ i, Finite (C i)]
    (m : ∀ i, C i → ℕ)
    (p q : ∀ i c, MvPolynomial (Fin (m i c)) R →ₐ[R] MvPolynomial (Fin (n i)) R)
    (hpq : ∀ i c, (Ideal.Quotient.mkₐ R (I i)).comp (p i c) =
      (Ideal.Quotient.mkₐ R (I i)).comp (q i c)) :
    ∃ t : ∀ i, Finset (I i), s ≤ t ∧
      (∀ e, FiniteRelationModel.relations (I (src e)) (t (src e)) ≤
        (FiniteRelationModel.relations (I (dst e)) (t (dst e))).comap (f e).toRingHom) ∧
      ∀ i c, (Ideal.Quotient.mkₐ R (FiniteRelationModel.relations (I i) (t i))).comp
        (p i c) =
          (Ideal.Quotient.mkₐ R (FiniteRelationModel.relations (I i) (t i))).comp (q i c) := by
  choose v hv using fun i ↦
    FiniteRelationModel.exists_equation_seeds (I i) (m i) (p i) (q i) (hpq i)
  classical
  obtain ⟨t, ht, hf'⟩ := exists_stable_stages n src dst f I hf (fun i ↦ s i ∪ v i)
  exact ⟨t, fun i ↦ Finset.subset_union_left.trans (ht i), hf',
    fun i ↦ hv i (t i) (Finset.subset_union_right.trans (ht i))⟩

end FLT.Mazur.FinitePolynomialCoefficients
