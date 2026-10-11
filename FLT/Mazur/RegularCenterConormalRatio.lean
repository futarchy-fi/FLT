/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterConormalQuotient
public import FLT.Mazur.RegularCenterOverlap

/-!
# Conormal characters determine actual exceptional fraction coordinates

The original fraction-chart lift divides generator quotients. After restriction
to the exceptional fiber, its ratios are controlled by the proved conormal classes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
open BlowupFractionChart
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) (ψ : B →+* C) (hψ : ψ d = 0)
  (a : A) (ha : a ∈ I) (hu : IsUnit (quotient I φ d hI a ha))

include hψ in
/-- An original conormal multiple gives the corresponding actual exceptional ratio value. -/
theorem unitQuotientLift_ratio_residue (b c : A) (hb : b ∈ I)
    (hbc : b - c * a ∈ I ^ 2) :
    ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) = ψ (φ c) := by
  apply (hu.map ψ).mul_right_inj.mp
  rw [← map_mul, quotient_mul_unitQuotientLift_ratio,
    quotient_residue_character I φ d hI hd ψ hψ b a c hb ha hbc]
  ring

include hψ in
/-- Equal conormal numerators give equal actual fraction coordinates on the exceptional fiber. -/
theorem unitQuotientLift_ratio_residue_congr (b c : A) (hb : b ∈ I) (hc : c ∈ I)
    (hbc : b - c ∈ I ^ 2) :
    ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) =
      ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a c hc)) := by
  apply (hu.map ψ).mul_right_inj.mp
  rw [← map_mul, ← map_mul, quotient_mul_unitQuotientLift_ratio,
    quotient_mul_unitQuotientLift_ratio]
  exact quotient_residue_eq_of_sub_mem_sq I φ d hI hd ψ hψ b c hb hc hbc

include hψ in
/-- Characters on numerator and denominator give their quotient on actual exceptional charts. -/
theorem unitQuotientLift_ratio_residue_characters
    (a' b b' ca cb : A) (ha' : a' ∈ I) (hb : b ∈ I) (hb' : b' ∈ I)
    (hu' : IsUnit (quotient I φ d hI a' ha'))
    (hea : a' - ca * a ∈ I ^ 2) (heb : b' - cb * b ∈ I ^ 2) :
    ψ (φ ca) * ψ (unitQuotientLift I φ d hI hd a' ha' hu' (ratio I a' b' hb')) =
      ψ (φ cb) * ψ (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) := by
  have hares := quotient_residue_character I φ d hI hd ψ hψ a' a ca ha' ha hea
  have hbres := quotient_residue_character I φ d hI hd ψ hψ b' b cb hb' hb heb
  have hleft := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a' ha' hu' b' hb')
  have hright := congrArg ψ
    (quotient_mul_unitQuotientLift_ratio I φ d hI hd a ha hu b hb)
  rw [map_mul, hares, hbres] at hleft
  rw [map_mul] at hright
  apply (hu.map ψ).mul_right_inj.mp
  linear_combination hleft - ψ (φ cb) * hright

end FLT.Mazur.RegularCenter
