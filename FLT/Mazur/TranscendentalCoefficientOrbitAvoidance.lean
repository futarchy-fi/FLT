/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTensorCoefficientConditions
public import FLT.Mazur.AffineRationalNonvanishing
public import FLT.Mazur.AlgebraicTensorRationalConjugacy
public import FLT.Mazur.AlgebraicTensorOrbitProduct
public import Mathlib.RingTheory.FiniteStability

/-!
# Entire algebraic point orbits avoiding transcendental coefficient conditions

The actual functions may have arbitrary transcendental coefficients. We
extract one nonzero algebraic coefficient condition, multiply its finite orbit,
and choose an algebraic rational point avoiding that product. Every conjugate
of this point satisfies every original extended function condition. There is
no descent or finite-orbit premise on the extended functions themselves.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
open scoped TensorProduct
open TensorCoefficientDetection AlgebraicTensorCoefficientOrbit
variable {k L K A J : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  [IsDomain (L ⊗[k] A)] [Finite J]

omit [IsAlgClosed L] [Algebra.FiniteType k A] in
/-- One original algebraic coefficient condition controls every conjugate and every function. -/
theorem exists_orbit_detecting_coefficient
    (x : J → K ⊗[L] (L ⊗[k] A)) (hx : ∀ j, x j ≠ 0) :
    ∃ a : L ⊗[k] A, a ≠ 0 ∧ ∀ p : L ⊗[k] A →ₐ[L] L,
      p a ≠ 0 → ∀ (σ : L ≃ₐ[k] L) (j : J),
        evaluation (K := K) (conjugatePoint p σ) (x j) ≠ 0 := by
  obtain ⟨c, hc, hd⟩ := exists_common_detecting_coefficient x hx
  refine ⟨orbitProduct c, orbitProduct_ne_zero c hc, fun p hp σ j ↦ ?_⟩
  apply hd (conjugatePoint p σ) ?_ j
  apply (conjugatePoint_ne_zero_iff p σ c).mpr
  exact all_conjugates_ne_zero p.toRingHom c hp σ.symm

/-- Construct a point whose entire residue-field conjugacy orbit satisfies the actual conditions. -/
theorem exists_point_all_conjugates
    (x : J → K ⊗[L] (L ⊗[k] A)) (hx : ∀ j, x j ≠ 0) :
    ∃ p : L ⊗[k] A →ₐ[L] L, ∀ (σ : L ≃ₐ[k] L) (j : J),
      evaluation (K := K) (conjugatePoint p σ) (x j) ≠ 0 := by
  obtain ⟨a, ha, hd⟩ := exists_orbit_detecting_coefficient x hx
  obtain ⟨p, hp⟩ := AffineRationalNonvanishing.exists_point_of_ne_zero (k := L) a ha
  exact ⟨p, hd p hp⟩

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
