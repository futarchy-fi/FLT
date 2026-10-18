/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuationPoleReciprocal
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Leading coefficients forced to vanish by a valuation pole

Every polynomial equation of a pole has nonunit leading coefficient. When
the equation uses the unchanged original scalar map, its leading coefficient
contracts into the original central prime. No polynomial equation is assumed to exist.
-/

@[expose] public noncomputable section
open Polynomial IsLocalRing
namespace FLT.Mazur.ValuationPoleReciprocal
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- The leading coefficient of any equation of a pole lies in the valuation maximal ideal. -/
theorem leadingCoeff_mem_maximalIdeal (x : K) (hx : x ∉ (algebraMap V K).range)
    (p : V[X]) (hp : p.eval₂ (algebraMap V K) x = 0) :
    p.leadingCoeff ∈ maximalIdeal V := by
  let _ : IsIntegrallyClosed V := (ValuationRing.integers V K).isIntegrallyClosed
  have hi : IsIntegral V (algebraMap V K p.leadingCoeff * x) :=
    (algebraMap V K).isIntegralElem_leadingCoeff_mul p x hp
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  change ¬ IsUnit p.leadingCoeff
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  apply hx
  refine ⟨w * z, ?_⟩
  rw [map_mul, hz, ← mul_assoc, ← map_mul, mul_comm w, hw, map_one, one_mul]

variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (t : R →+* V) (φ : B →+* K)

/-- Every original-scalar equation of a pole has leading coefficient in the contracted center. -/
theorem original_leadingCoeff_mem (hcomm : φ.comp s = (algebraMap V K).comp t)
    (b : B) (hb : φ b ∉ (algebraMap V K).range)
    (p : R[X]) (hp : p.eval₂ s b = 0) :
    t p.leadingCoeff ∈ maximalIdeal V := by
  by_contra hn
  have hu : IsUnit (t p.leadingCoeff) := by
    exact not_not.mp hn
  have he : (p.map t).eval₂ (algebraMap V K) (φ b) = 0 := by
    rw [eval₂_map, ← hcomm, ← hom_eval₂, hp, map_zero]
  have hm := leadingCoeff_mem_maximalIdeal V K (φ b) hb (p.map t) he
  rw [leadingCoeff_map_of_leadingCoeff_ne_zero t hu.ne_zero] at hm
  exact hn hm

end FLT.Mazur.ValuationPoleReciprocal
