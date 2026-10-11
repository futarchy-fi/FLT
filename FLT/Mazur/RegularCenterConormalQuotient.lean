/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterRatioCover

/-!
# First-order center data determines exceptional quotients

For a regular principalized center, a function in the square of the center
has quotient divisible by the retained denominator. On the exceptional fiber,
quotients therefore depend only on the original conormal class.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d)

include hd in
/-- Division by the regular principal generator preserves subtraction. -/
theorem quotient_sub (a b : A) (ha : a ∈ I) (hb : b ∈ I) :
    quotient I φ d hI (a - b) (I.sub_mem ha hb) =
      quotient I φ d hI a ha - quotient I φ d hI b hb := by
  apply hd.left
  dsimp only
  rw [denominator_mul_quotient, mul_sub, denominator_mul_quotient,
    denominator_mul_quotient, map_sub]

include hd in
/-- Division is linear in original coefficient functions. -/
theorem quotient_mul_left (c b : A) (hb : b ∈ I) :
    quotient I φ d hI (c * b) (I.mul_mem_left c hb) =
      φ c * quotient I φ d hI b hb := by
  apply hd.left
  dsimp only
  rw [denominator_mul_quotient, mul_left_comm, denominator_mul_quotient, map_mul]

include hd in
/-- A function in the square of the center has a quotient in the principal center. -/
theorem quotient_mem_denominator_of_mem_sq (a : A) (ha : a ∈ I) (ha₂ : a ∈ I ^ 2) :
    quotient I φ d hI a ha ∈ Ideal.span {d} := by
  have h : φ a ∈ (Ideal.span {d}) ^ 2 := by
    rw [← hI, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ ha₂
  rw [Ideal.span_singleton_pow] at h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h
  have he : quotient I φ d hI a ha = d * b := by
    apply hd.left
    dsimp only
    rw [denominator_mul_quotient, hb]
    ring
  rw [he]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton d))

variable (ψ : B →+* C) (hψ : ψ d = 0)

include hd hψ in
/-- Quadratic center terms vanish after division and restriction to the exceptional fiber. -/
theorem quotient_residue_eq_zero_of_mem_sq (a : A) (ha : a ∈ I) (ha₂ : a ∈ I ^ 2) :
    ψ (quotient I φ d hI a ha) = 0 := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    (quotient_mem_denominator_of_mem_sq I φ d hI hd a ha ha₂)
  rw [hb, map_mul, hψ, zero_mul]

include hd hψ in
/-- Equal original conormal classes have equal exceptional quotient coordinates. -/
theorem quotient_residue_eq_of_sub_mem_sq (a b : A) (ha : a ∈ I) (hb : b ∈ I)
    (hab : a - b ∈ I ^ 2) :
    ψ (quotient I φ d hI a ha) = ψ (quotient I φ d hI b hb) := by
  have h := quotient_residue_eq_zero_of_mem_sq I φ d hI hd ψ hψ
    (a - b) (I.sub_mem ha hb) hab
  rw [quotient_sub I φ d hI hd, map_sub, sub_eq_zero] at h
  exact h

include hd hψ in
/-- A scalar conormal character becomes the same character on actual exceptional quotients. -/
theorem quotient_residue_character (a b c : A) (ha : a ∈ I) (hb : b ∈ I)
    (hab : a - c * b ∈ I ^ 2) :
    ψ (quotient I φ d hI a ha) = ψ (φ c) * ψ (quotient I φ d hI b hb) := by
  rw [← map_mul, ← quotient_mul_left I φ d hI hd]
  exact quotient_residue_eq_of_sub_mem_sq I φ d hI hd ψ hψ
    a (c * b) ha (I.mul_mem_left c hb) hab

end FLT.Mazur.RegularCenter
