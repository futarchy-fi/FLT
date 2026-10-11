/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterConormalQuotient

/-!
# Residue conormal relations survive regular principalization

Division by the regular center generator sends `J*I` into the image of `J`.
Consequently both quadratic center terms and base-times-center terms vanish
on the residue exceptional fiber, without discarding a higher-power base generator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (I J : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d)

include hd in
/-- Regular division removes one center factor from a product ideal. -/
theorem quotient_mem_map_of_mem_product (a : A) (ha : a ∈ I) (haJ : a ∈ J * I) :
    quotient I φ d hI a ha ∈ J.map φ := by
  have h : φ a ∈ J.map φ * Ideal.span {d} := by
    rw [← hI, ← Ideal.map_mul]
    exact Ideal.mem_map_of_mem φ haJ
  obtain ⟨c, hc, he⟩ := Ideal.mem_mul_span_singleton.mp h
  have heq : quotient I φ d hI a ha = c := by
    apply hd.left
    dsimp only
    rw [denominator_mul_quotient, ← he, mul_comm c d]
  exact heq.symm ▸ hc

variable (ψ : B →+* C) (hψ : ψ d = 0) (hJ : J ≤ RingHom.ker (ψ.comp φ))

include hd hψ hJ in
/-- The entire residue conormal relation ideal vanishes after regular division. -/
theorem quotient_residue_eq_zero_of_mem_residue_conormal
    (a : A) (ha : a ∈ I) (haJ : a ∈ I ^ 2 + J * I) :
    ψ (quotient I φ d hI a ha) = 0 := by
  have hrel : a ∈ (I + J) * I := by
    simpa only [add_mul, pow_two] using haJ
  have h := quotient_mem_map_of_mem_product I (I + J) φ d hI hd a ha hrel
  have hle : (I + J).map φ ≤ RingHom.ker ψ := by
    rw [show I + J = I ⊔ J from rfl, Ideal.map_sup]
    apply sup_le
    · rw [hI, Ideal.span_singleton_le_iff_mem]
      exact hψ
    · exact Ideal.map_le_iff_le_comap.mpr hJ
  exact hle h

include hd hψ hJ in
/-- Residue conormal equality gives equality of the actual exceptional quotients. -/
theorem quotient_residue_eq_of_sub_mem_residue_conormal
    (a b : A) (ha : a ∈ I) (hb : b ∈ I) (hab : a - b ∈ I ^ 2 + J * I) :
    ψ (quotient I φ d hI a ha) = ψ (quotient I φ d hI b hb) := by
  have h := quotient_residue_eq_zero_of_mem_residue_conormal I J φ d hI hd ψ hψ hJ
    (a - b) (I.sub_mem ha hb) hab
  rw [quotient_sub I φ d hI hd, map_sub, sub_eq_zero] at h
  exact h

include hd hψ hJ in
/-- A residue conormal character acts on genuine exceptional quotient coordinates. -/
theorem quotient_residue_character_of_mem_residue_conormal
    (a b c : A) (ha : a ∈ I) (hb : b ∈ I) (hab : a - c * b ∈ I ^ 2 + J * I) :
    ψ (quotient I φ d hI a ha) = ψ (φ c) * ψ (quotient I φ d hI b hb) := by
  rw [← map_mul, ← quotient_mul_left I φ d hI hd]
  exact quotient_residue_eq_of_sub_mem_residue_conormal I J φ d hI hd ψ hψ hJ
    a (c * b) ha (I.mul_mem_left c hb) hab

include hd hψ hJ in
/-- A balanced character identity needs no choice of an inverse before specialization. -/
theorem quotient_residue_balanced_character
    (a b ca cb : A) (ha : a ∈ I) (hb : b ∈ I)
    (hab : ca * a - cb * b ∈ I ^ 2 + J * I) :
    ψ (φ ca) * ψ (quotient I φ d hI a ha) =
      ψ (φ cb) * ψ (quotient I φ d hI b hb) := by
  have h := quotient_residue_eq_of_sub_mem_residue_conormal I J φ d hI hd ψ hψ hJ
    (ca * a) (cb * b) (I.mul_mem_left ca ha) (I.mul_mem_left cb hb) hab
  rw [quotient_mul_left I φ d hI hd ca a ha,
    quotient_mul_left I φ d hI hd cb b hb, map_mul, map_mul] at h
  exact h

end FLT.Mazur.RegularCenter
