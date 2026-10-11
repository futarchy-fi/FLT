/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# One denominator for finitely many residue coordinates

Residue-field coordinates at arbitrary primes need not lift to the original
ring. A single element outside the prime clears all finitely many coordinates,
so a principal-open base neighborhood suffices for coordinate slicing.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ResidueCoordinateDenominators
variable {R K : Type} [CommRing R] [Field K]

/-- A map to a field that is surjective on stalks expresses each value as a fraction. -/
theorem exists_fraction (φ : R →+* K) (hφ : φ.SurjectiveOnStalks) (z : K) :
    ∃ a r : R, φ r ≠ 0 ∧ φ r * z = φ a := by
  obtain ⟨a, r, c, hc, hr, he⟩ :=
    (RingHom.surjective_localRingHom_iff (f := φ) (⊥ : Ideal K)).mp (hφ _ inferInstance) z
  have hc' : c ≠ 0 := by simpa only [Ideal.mem_bot] using hc
  refine ⟨a, r, by simpa only [Ideal.mem_bot] using hr, ?_⟩
  exact mul_left_cancel₀ hc' (by simpa only [mul_assoc] using he)

/-- Finitely many field values have one common denominator over a stalk-surjective base. -/
theorem exists_common_denominator (φ : R →+* K) (hφ : φ.SurjectiveOnStalks)
    {n : ℕ} (v : Fin n → K) :
    ∃ r : R, φ r ≠ 0 ∧ ∃ a : Fin n → R, ∀ i, φ (a i) = φ r * v i := by
  induction n with
  | zero =>
    exact ⟨1, by rw [map_one]; exact one_ne_zero, Fin.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨r, hr, a, ha⟩ := ih (fun i ↦ v i.succ)
    obtain ⟨b, s, hs, hb⟩ := exists_fraction φ hφ (v 0)
    refine ⟨r * s, by rw [map_mul]; exact mul_ne_zero hr hs,
      Fin.cons (r * b) (fun i ↦ s * a i), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero, map_mul, ← hb, mul_assoc]
    · simp only [Fin.cons_succ, map_mul, ha, mul_assoc, mul_left_comm]

/-- Arbitrary residue-field coordinates clear on a principal open containing the base prime. -/
theorem exists_residue_denominator (p : Ideal R) [p.IsPrime] {n : ℕ}
    (v : Fin n → p.ResidueField) :
    ∃ r : R, algebraMap R p.ResidueField r ≠ 0 ∧
      ∃ a : Fin n → R, ∀ i,
        algebraMap R p.ResidueField (a i) = algebraMap R p.ResidueField r * v i :=
  exists_common_denominator _ p.surjectiveOnStalks_residueField v

/-- The finite coordinate vector lifts on one actual principal-open coefficient ring. -/
theorem exists_localized_coordinates (φ : R →+* K) (hφ : φ.SurjectiveOnStalks)
    {n : ℕ} (v : Fin n → K) :
    ∃ (r : R) (_ : φ r ≠ 0) (ψ : Localization.Away r →+* K),
      ψ.comp (algebraMap R (Localization.Away r)) = φ ∧
        ∃ a : Fin n → Localization.Away r, ∀ i, ψ (a i) = v i := by
  obtain ⟨r, hr, a, ha⟩ := exists_common_denominator φ hφ v
  let ψ : Localization.Away r →+* K :=
    IsLocalization.Away.lift r (isUnit_iff_ne_zero.mpr hr)
  refine ⟨r, hr, ψ, IsLocalization.Away.lift_comp _ _,
    fun i ↦ IsLocalization.mk' (Localization.Away r) (a i) ⟨r, Submonoid.mem_powers r⟩, ?_⟩
  intro i
  exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (ha i)

end FLT.Mazur.ResidueCoordinateDenominators
