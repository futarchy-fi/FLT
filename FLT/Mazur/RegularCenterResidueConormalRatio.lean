/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterResidueConormal
public import FLT.Mazur.RegularCenterOverlap

/-!
# Actual fraction coordinates from residue conormal characters

The regular-center fraction lifts respect the relations `I² + J*I` after
specializing to the residue exceptional fiber.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
open BlowupFractionChart
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (I J : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) (ψ : B →+* C) (hψ : ψ d = 0)
  (hJ : J ≤ RingHom.ker (ψ.comp φ))
  (a : A) (ha : a ∈ I) (hu : IsUnit (quotient I φ d hI a ha))

include hψ hJ in
/-- Balanced residue characters control the actual fraction numerators. -/
theorem unitQuotientLift_ratio_residue_balanced_character
    (b c cb cc : A) (hb : b ∈ I) (hc : c ∈ I)
    (hbc : cb * b - cc * c ∈ I ^ 2 + J * I) :
    ψ (φ cb) * ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) =
      ψ (φ cc) * ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a c hc)) := by
  have h := quotient_residue_balanced_character I J φ d hI hd ψ hψ hJ
    b c cb cc hb hc hbc
  have hbq := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a ha hu b hb)
  have hcq := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a ha hu c hc)
  simp only [map_mul] at hbq hcq
  apply (hu.map ψ).mul_right_inj.mp
  linear_combination h + ψ (φ cb) * hbq - ψ (φ cc) * hcq

include hψ hJ in
/-- Separate residue characters on numerator and denominator yield the actual transformed ratio. -/
theorem unitQuotientLift_ratio_residue_conormal_characters
    (a' b b' ca cb : A) (ha' : a' ∈ I) (hb : b ∈ I) (hb' : b' ∈ I)
    (hu' : IsUnit (quotient I φ d hI a' ha'))
    (hea : a' - ca * a ∈ I ^ 2 + J * I) (heb : b' - cb * b ∈ I ^ 2 + J * I) :
    ψ (φ ca) * ψ (unitQuotientLift I φ d hI hd a' ha' hu' (ratio I a' b' hb')) =
      ψ (φ cb) * ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) := by
  have hares := quotient_residue_character_of_mem_residue_conormal
    I J φ d hI hd ψ hψ hJ a' a ca ha' ha hea
  have hbres := quotient_residue_character_of_mem_residue_conormal
    I J φ d hI hd ψ hψ hJ b' b cb hb' hb heb
  have hleft := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a' ha' hu' b' hb')
  have hright := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a ha hu b hb)
  rw [map_mul, hares, hbres] at hleft
  rw [map_mul] at hright
  apply (hu.map ψ).mul_right_inj.mp
  linear_combination hleft - ψ (φ cb) * hright

end FLT.Mazur.RegularCenter
