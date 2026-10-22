/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarClearedPolynomialAnnihilator
public import FLT.Mazur.ScalarPolynomialResidueRigidity

/-!
# Residue rigidity from scalar polynomial equations in source stalks

Equations need only hold in the localization at the inverse image of the
test prime. Clearing them constructs actual global differential annihilators
which avoid that prime. The generators need span only the differential module;
they need not generate the algebra. All primes, including embedded ones, work.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalPolynomialResidueRigidity
open Polynomial
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]

/-- A cleared equation still has a nonzero derivative at a separable residue root. -/
theorem derivative_image_ne_zero {K : Type} [CommRing K] [IsDomain K]
    (φ : A →+* K) (x t : A) (P : R[X]) (hP : t * aeval x P = 0)
    (ht : φ t ≠ 0) (hs : (P.map (φ.comp (algebraMap R A))).Separable) :
    φ (aeval x P.derivative) ≠ 0 := by
  have he (F : R[X]) : (F.map (φ.comp (algebraMap R A))).eval (φ x) =
      φ (aeval x F) := by
    rw [eval_map, ← hom_eval₂]
    rfl
  have hz : (P.map (φ.comp (algebraMap R A))).eval (φ x) = 0 := by
    rw [he]
    apply (mul_eq_zero.mp _).resolve_left ht
    rw [← map_mul, hP, map_zero]
  have hn := hs.eval₂_derivative_ne_zero (RingHom.id K) hz
  simpa only [eval₂_id, derivative_map, he] using hn

/-- A clearing element outside the test prime preserves derivative avoidance. -/
theorem cleared_derivative_not_mem (φ : A →+* B) (Q : PrimeSpectrum B)
    (x t : A) (P : R[X]) (hP : t * aeval x P = 0) (ht : φ t ∉ Q.asIdeal)
    (hs : (P.map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) :
    φ (t ^ 2 * aeval x P.derivative) ∉ Q.asIdeal := by
  have ht' : ((algebraMap B Q.asIdeal.ResidueField).comp φ) t ≠ 0 :=
    fun h ↦ ht (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hd := derivative_image_ne_zero
    ((algebraMap B Q.asIdeal.ResidueField).comp φ) x t P hP ht' hs
  intro h
  have hz := Ideal.algebraMap_residueField_eq_zero.mpr h
  exact mul_ne_zero (pow_ne_zero 2 ht') hd (by
    simpa only [map_mul, map_pow, RingHom.comp_apply] using hz)

/-- Cleared equations and differential generators give one annihilator avoiding the test prime. -/
theorem exists_annihilator_of_cleared {ι : Type} [Finite ι]
    (φ : A →+* B) (Q : PrimeSpectrum B) (z t : ι → A) (P : ι → R[X])
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval (z i) (P i) = 0) (ht : ∀ i, φ (t i) ∉ Q.asIdeal)
    (hs : ∀ i, ((P i).map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := Fintype.ofFinite ι
  refine ⟨_, ScalarClearedPolynomialAnnihilator.product_mem_annihilator z t P hz hP, ?_⟩
  rw [map_prod]
  intro h
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact cleared_derivative_not_mem φ Q (z i) (t i) (P i) (hP i) (ht i) (hs i) hi

/-- Relations in the actual source stalk suffice; the clearing elements are constructed. -/
theorem exists_annihilator_of_local {ι : Type} [Finite ι]
    (φ : A →+* B) (Q : PrimeSpectrum B) (z : ι → A) (P : ι → R[X])
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval (z i) (P i)) = 0)
    (hs : ∀ i, ((P i).map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  have hc (i : ι) : ∃ t : (PrimeSpectrum.comap φ Q).asIdeal.primeCompl,
      (t : A) * aeval (z i) (P i) = 0 :=
    (IsLocalization.map_eq_zero_iff (PrimeSpectrum.comap φ Q).asIdeal.primeCompl
      (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) _).mp (hP i)
  choose t ht using hc
  exact exists_annihilator_of_cleared φ Q z (fun i ↦ t i) P hz ht
    (fun i ↦ (t i).property) hs

end FLT.Mazur.ScalarLocalPolynomialResidueRigidity
