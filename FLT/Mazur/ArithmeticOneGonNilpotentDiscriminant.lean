/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonInfinitesimalDiscriminant

/-!
# Every nilpotent discriminant has an arithmetic degeneration parameter

Finite iteration solves the actual discriminant equation over any commutative
ring. Nilpotence makes the iteration stationary, so no completeness or
inversion of residue characteristics is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ArithmeticOneGonParameter
open OneGonSmoothing
variable {R : Type} [CommRing R]

/-- Successive polynomial approximations to the prescribed discriminant. -/
def discriminantApproximation (d : R) : ℕ → R
  | 0 => 0
  | n + 1 => -d - 432 * discriminantApproximation d n ^ 2

/-- Each approximation lies in the original discriminant's principal ideal. -/
theorem discriminantApproximation_dvd (d : R) (n : ℕ) :
    d ∣ discriminantApproximation d n := by
  induction n with
  | zero => exact dvd_zero d
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨-1 - 432 * d * a ^ 2, ?_⟩
    rw [discriminantApproximation, ha]
    ring

/-- Each iteration improves the error by another power of the original discriminant. -/
theorem discriminantApproximation_difference_dvd (d : R) (n : ℕ) :
    d ^ (n + 1) ∣ discriminantApproximation d (n + 1) - discriminantApproximation d n := by
  induction n with
  | zero =>
    refine ⟨-1, ?_⟩
    simp [discriminantApproximation]
  | succ n ih =>
    obtain ⟨a, ha⟩ := discriminantApproximation_dvd d (n + 1)
    obtain ⟨b, hb⟩ := discriminantApproximation_dvd d n
    obtain ⟨c, hc⟩ := ih
    refine ⟨-432 * c * (a + b), ?_⟩
    calc
      _ = -432 *
          (discriminantApproximation d (n + 1) - discriminantApproximation d n) *
          (discriminantApproximation d (n + 1) + discriminantApproximation d n) := by
        conv_lhs => lhs; rw [discriminantApproximation]
        conv_lhs => rhs; rw [discriminantApproximation]
        ring
      _ = _ := by rw [hc, ha, hb, pow_succ d (n + 1)]; ring

/-- A vanishing discriminant power makes the polynomial approximation stationary. -/
theorem discriminantApproximation_stationary (d : R) (n : ℕ) (hd : d ^ n = 0) :
    discriminantApproximation d (n + 1) = discriminantApproximation d n := by
  have h := discriminantApproximation_difference_dvd d n
  rw [pow_succ, hd, zero_mul, zero_dvd_iff] at h
  exact sub_eq_zero.mp h

/-- Every nilpotent discriminant has a unique nilpotent parameter in the explicit family. -/
theorem exists_unique_nilpotent_discriminant (d : R) (hd : IsNilpotent d) :
    ∃! t : {t : R // IsNilpotent t}, (equation t.val).Δ = d := by
  obtain ⟨n, hn⟩ := hd
  let t := discriminantApproximation d n
  obtain ⟨a, ha⟩ := discriminantApproximation_dvd d n
  have ht : IsNilpotent t := by
    change IsNilpotent (discriminantApproximation d n)
    rw [ha]
    exact (Commute.all d a).isNilpotent_mul_right ⟨n, hn⟩
  have hs : -d - 432 * t ^ 2 = t := discriminantApproximation_stationary d n hn
  have he : (equation t).Δ = d := by
    rw [equation_discriminant]
    calc
      _ = (-d - 432 * t ^ 2 - t) + d := by ring
      _ = d := by rw [hs, sub_self, zero_add]
  refine ⟨⟨t, ht⟩, he, ?_⟩
  intro s hs
  exact Subtype.ext (nilpotent_discriminant_injective s.property ht (hs.trans he.symm))

/-- A nilpotent discriminant classifies a unique infinitesimal point of the algebraic base. -/
theorem exists_unique_nilpotent_discriminant_hom (d : R) (hd : IsNilpotent d) :
    ∃! f : ParameterRing →+* R,
      IsNilpotent (f parameter) ∧ f (equation parameter).Δ = d := by
  obtain ⟨t, ht, _⟩ := exists_unique_nilpotent_discriminant d hd
  have hu : IsUnit (1 + 432 * t.val) :=
    ((Commute.all 432 t.val).isNilpotent_mul_left t.property).isUnit_one_add
  let f := specialize t.val hu
  have hf : f parameter = t.val := specialize_parameter _ _
  have he : f (equation parameter).Δ = d := by
    rw [← WeierstrassCurve.map_Δ, equation_map, hf]
    exact ht
  refine ⟨f, ⟨hf.symm ▸ t.property, he⟩, ?_⟩
  intro g hg
  exact infinitesimal_hom_ext g f hg.1 (hf.symm ▸ t.property) (hg.2.trans he.symm)

end FLT.Mazur.ArithmeticOneGonParameter
