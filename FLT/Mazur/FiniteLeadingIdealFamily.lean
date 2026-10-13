/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Finsupp.PWO
public import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# Finite leading families for polynomial ideals

Dickson's lemma selects finitely many actual nonzero members of an ideal whose
leading monomials divide every leading monomial in the ideal. Over a domain,
the product of their leading coefficients is a nonzero denominator. This is
the finite input to generic freeness, without an assumed Groebner basis.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace FLT.Mazur.FiniteLeadingIdealFamily
variable {σ R : Type*} [Finite σ] [CommRing R]
  (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))

/-- Finitely many actual ideal elements control all nonzero leading monomials. -/
theorem exists_family : ∃ s : Finset (MvPolynomial σ R),
    (∀ b ∈ s, b ∈ I ∧ b ≠ 0) ∧
    ∀ p ∈ I, p ≠ 0 → ∃ b ∈ s, m.degree b ≤ m.degree p := by
  classical
  let D : Set (σ →₀ ℕ) := m.degree '' {p : MvPolynomial σ R | p ∈ I ∧ p ≠ 0}
  let M : Set (σ →₀ ℕ) := {a | Minimal (· ∈ D) a}
  have hM : M.Finite := WellQuasiOrderedLE.finite_of_isAntichain
    (setOfPred_minimal_antichain (· ∈ D))
  have hrep (a : M) : ∃ p : MvPolynomial σ R, (p ∈ I ∧ p ≠ 0) ∧ m.degree p = a :=
    a.property.1
  choose b hb using hrep
  let s := hM.toFinset.attach.image fun a ↦ b ⟨a.val, hM.mem_toFinset.mp a.property⟩
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hb _).1
  · intro p hp hp0
    obtain ⟨a, hap, ha⟩ := (Set.isPWO_of_wellQuasiOrderedLE D).exists_le_minimal
      (Set.mem_image_of_mem m.degree ⟨hp, hp0⟩)
    refine ⟨b ⟨a, ha⟩, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨⟨a, hM.mem_toFinset.mpr ha⟩, Finset.mem_attach _ _, rfl⟩
    · rw [(hb ⟨a, ha⟩).2]
      exact hap

/-- A selected finite family consists of original ideal elements, not new equations. -/
def family : Finset (MvPolynomial σ R) := (exists_family m I).choose

theorem family_mem (b : MvPolynomial σ R) (hb : b ∈ family m I) : b ∈ I :=
  ((exists_family m I).choose_spec.1 b hb).1

theorem family_ne_zero (b : MvPolynomial σ R) (hb : b ∈ family m I) : b ≠ 0 :=
  ((exists_family m I).choose_spec.1 b hb).2

/-- Every nonzero original equation has a leading divisor in the finite family. -/
theorem family_covers (p : MvPolynomial σ R) (hp : p ∈ I) (hp0 : p ≠ 0) :
    ∃ b ∈ family m I, m.degree b ≤ m.degree p :=
  (exists_family m I).choose_spec.2 p hp hp0

/-- One coefficient denominator makes all selected leading coefficients units. -/
def denominator : R := ∏ b ∈ family m I, m.leadingCoeff b

theorem denominator_ne_zero [IsDomain R] : denominator m I ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  exact m.leadingCoeff_ne_zero_iff.mpr (family_ne_zero m I b hb)

/-- Inverting the product inverts every selected coefficient, in any target ring. -/
theorem leadingCoeff_isUnit {S : Type*} [CommRing S] (φ : R →+* S)
    (hφ : IsUnit (φ (denominator m I))) (b : MvPolynomial σ R)
    (hb : b ∈ family m I) : IsUnit (φ (m.leadingCoeff b)) := by
  classical
  rw [denominator, map_prod] at hφ
  exact IsUnit.prod_iff.mp hφ b hb

end FLT.Mazur.FiniteLeadingIdealFamily
