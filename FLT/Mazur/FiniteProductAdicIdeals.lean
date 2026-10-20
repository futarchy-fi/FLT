/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicIdealPowerComparison
public import Mathlib.RingTheory.Ideal.Prod

/-!
# Exact powers and scalar support in finite equation rings

A finite product of coordinate ideals is one ideal whose powers are exactly
the coordinate powers. Whole scalar-fiber support is equivalent to the support
condition in every coordinate; no coordinate may be discarded.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteProductAdicIdeals
variable {ι : Type*} [Finite ι] {B : ι → Type*} [∀ i, CommRing (B i)]

/-- Full finite product ideals retain their exact powers coordinate by coordinate. -/
theorem pi_pow (K : ∀ i, Ideal (B i)) (n : ℕ) :
    (Ideal.pi K) ^ n = Ideal.pi (fun i ↦ K i ^ n) := by
  apply (Ideal.piOrderIso (R := B)).injective
  funext i
  change Ideal.map (Pi.evalRingHom B i) _ = Ideal.map (Pi.evalRingHom B i) _
  rw [Ideal.map_pow, Ideal.map_evalRingHom_pi, Ideal.map_evalRingHom_pi]

/-- Membership in one full error power tests every coordinate at the same order. -/
theorem mem_pi_pow (K : ∀ i, Ideal (B i)) (n : ℕ) (x : ∀ i, B i) :
    x ∈ (Ideal.pi K) ^ n ↔ ∀ i, x i ∈ K i ^ n := by
  rw [pi_pow]
  rfl

/-- Finite products also retain the entire radical, using one bound for all coordinates. -/
theorem pi_radical (K : ∀ i, Ideal (B i)) :
    (Ideal.pi K).radical = Ideal.pi (fun i ↦ (K i).radical) := by
  classical
  let _ := Fintype.ofFinite ι
  ext x
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n, hn i⟩
  · intro hx
    choose n hn using hx
    refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
    exact (K i).pow_mem_of_pow_mem (hn i) (Finset.le_sup (Finset.mem_univ i))

variable {C D : Type*} [CommRing C] [CommRing D]

/-- The boundary block and the mixed block also retain their exact powers. -/
theorem prod_pow (K : Ideal C) (L : Ideal D) (n : ℕ) :
    K.prod L ^ n = (K ^ n).prod (L ^ n) := by
  apply (Ideal.idealProdEquiv (R := C) (S := D)).injective
  apply Prod.ext
  · change Ideal.map (RingHom.fst C D) _ = Ideal.map (RingHom.fst C D) _
    rw [Ideal.map_pow, Ideal.map_fst_prod, Ideal.map_fst_prod]
  · change Ideal.map (RingHom.snd C D) _ = Ideal.map (RingHom.snd C D) _
    rw [Ideal.map_pow, Ideal.map_snd_prod, Ideal.map_snd_prod]

variable {R : Type*} [CommRing R] [∀ i, Algebra R (B i)]

/-- Scalar extension to a finite product is the product of scalar extensions. -/
theorem scalar_map_pi (J : Ideal R) :
    J.map (algebraMap R (∀ i, B i)) = Ideal.pi (fun i ↦ J.map (algebraMap R (B i))) := by
  apply (Ideal.piOrderIso (R := B)).injective
  funext i
  change Ideal.map (Pi.evalRingHom B i) _ = Ideal.map (Pi.evalRingHom B i) _
  rw [Ideal.map_map, Ideal.map_evalRingHom_pi]
  rfl

/-- Radical containment in the full equation ring is equivalent to every coordinate test. -/
theorem pi_le_scalar_radical_iff (J : Ideal R) (K : ∀ i, Ideal (B i)) :
    Ideal.pi K ≤ (J.map (algebraMap R (∀ i, B i))).radical ↔
      ∀ i, K i ≤ (J.map (algebraMap R (B i))).radical := by
  rw [scalar_map_pi, pi_radical, Ideal.pi_le_pi_iff]
  rfl

/-- Whole scalar-fiber support in each coordinate gives whole support in the product. -/
theorem pi_scalar_support (J : Ideal R) (K : ∀ i, Ideal (B i))
    (h : ∀ i, PrimeSpectrum.zeroLocus (J.map (algebraMap R (B i)) : Set (B i)) ⊆
      PrimeSpectrum.zeroLocus (K i : Set (B i))) :
    PrimeSpectrum.zeroLocus (J.map (algebraMap R (∀ i, B i)) : Set (∀ i, B i)) ⊆
      PrimeSpectrum.zeroLocus (Ideal.pi K : Set (∀ i, B i)) := by
  apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mpr
  exact (pi_le_scalar_radical_iff J K).mpr fun i ↦
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp (h i)

end FLT.Mazur.FiniteProductAdicIdeals
