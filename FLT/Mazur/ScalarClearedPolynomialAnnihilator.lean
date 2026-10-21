/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteDifferentialGenerators

/-!
# Differential annihilators from equations valid after localization

If `t * P(x) = 0`, differentiation shows that `t² * P'(x)` kills `dx`.
The square accounts for the differential of the denominator; no cancellation
or reducedness is used. Products of these elements annihilate the full module
when the root differentials generate, without finite algebra generation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarClearedPolynomialAnnihilator
open Polynomial
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- Clearing a relation costs a square of the clearing element after differentiation. -/
theorem cleared_derivative_smul_d_eq_zero (x t : A) (P : R[X])
    (hP : t * aeval x P = 0) :
    (t ^ 2 * aeval x P.derivative) • KaehlerDifferential.D R A x = 0 := by
  have h := congrArg (fun a ↦ t • KaehlerDifferential.D R A a) hP
  rw [Derivation.leibniz, smul_add, Derivation.map_aeval] at h
  simp only [smul_smul, hP, zero_smul, add_zero, map_zero, smul_zero] at h
  simpa only [pow_two, mul_assoc] using h

/-- Common multiples of cleared derivatives annihilate all relative differentials. -/
theorem common_multiple_mem_annihilator {ι : Type} (z t : ι → A) (P : ι → R[X])
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval (z i) (P i) = 0)
    (a : A) (ha : ∀ i, (t i ^ 2 * aeval (z i) (P i).derivative) ∣ a) :
    a ∈ Module.annihilator A (KaehlerDifferential R A) := by
  apply ScalarFiniteDifferentialGenerators.mem_annihilator z hz a
  intro i
  obtain ⟨b, hb⟩ := ha i
  rw [hb, mul_comm, mul_smul, cleared_derivative_smul_d_eq_zero _ _ _ (hP i), smul_zero]

/-- The product of cleared derivatives is an explicit full differential annihilator. -/
theorem product_mem_annihilator {ι : Type} [Fintype ι] (z t : ι → A) (P : ι → R[X])
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval (z i) (P i) = 0) :
    (∏ i, (t i ^ 2 * aeval (z i) (P i).derivative)) ∈
      Module.annihilator A (KaehlerDifferential R A) := by
  apply common_multiple_mem_annihilator z t P hz hP
  intro i
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- Cleared equations construct a formally unramified principal localization. -/
theorem product_away_formallyUnramified {ι : Type} [Fintype ι]
    (z t : ι → A) (P : ι → R[X])
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval (z i) (P i) = 0) :
    Algebra.FormallyUnramified R
      (Localization.Away (∏ i, (t i ^ 2 * aeval (z i) (P i).derivative))) :=
  ScalarDifferentialPrincipalRigidity.away_formallyUnramified _
    (product_mem_annihilator z t P hz hP)

end FLT.Mazur.ScalarClearedPolynomialAnnihilator
