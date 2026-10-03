/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicDegree

/-! # Relative degrees in the actual cyclotomic tower -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open IntermediateField
variable (p : ℕ) [hp : Fact p.Prime]

/-- The higher cyclotomic level, regarded as an extension of the lower level. -/
def padicCyclotomicRelative (n r : ℕ) :
    IntermediateField (padicCyclotomicTower p (n + 1)) (PadicAlgCl p) :=
  extendScalars (padicCyclotomicTower_mono p (show n + 1 ≤ n + r + 1 by omega))

/-- Relative levels are finite extensions of their lower level. -/
instance instFiniteDimensionalPadicCyclotomicRelative (n r : ℕ) :
    FiniteDimensional (padicCyclotomicTower p (n + 1)) (padicCyclotomicRelative p n r) := by
  have : FiniteDimensional ℚ_[p] (padicCyclotomicRelative p n r) :=
    instFiniteDimensionalPadicCyclotomicTower p (n + r + 1)
  exact FiniteDimensional.right ℚ_[p] (padicCyclotomicTower p (n + 1)) _

/-- Above the first level, r steps have precisely degree p^r. -/
theorem padicCyclotomicRelative_finrank (n r : ℕ) :
    Module.finrank (padicCyclotomicTower p (n + 1)) (padicCyclotomicRelative p n r) =
      p ^ r := by
  have ht := Module.finrank_mul_finrank ℚ_[p] (padicCyclotomicTower p (n + 1))
    (padicCyclotomicRelative p n r)
  change Module.finrank ℚ_[p] (padicCyclotomicTower p (n + 1)) * _ =
    Module.finrank ℚ_[p] (padicCyclotomicTower p (n + r + 1)) at ht
  rw [padicCyclotomicTower_finrank, padicCyclotomicTower_finrank, pow_add] at ht
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp.out.pos n)
    (Nat.sub_pos_of_lt hp.out.one_lt))
  calc
    _ = p ^ n * p ^ r * (p - 1) := ht
    _ = _ := by ring

/-- A primitive root at the upper level generates the relative extension. -/
theorem padicCyclotomicRelative_eq_adjoin (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + r + 1))) :
    padicCyclotomicRelative p n r = adjoin (padicCyclotomicTower p (n + 1)) {ζ} := by
  apply restrictScalars_injective ℚ_[p]
  rw [restrictScalars_adjoin, adjoin_union, adjoin_self]
  change padicCyclotomicTower p (n + r + 1) = _
  rw [← padicCyclotomicTower_eq_adjoin p _ ζ hζ,
    sup_eq_right.mpr (padicCyclotomicTower_mono p (by omega))]

/-- The relative minimal polynomial of a primitive upper root has degree p^r. -/
theorem padicCyclotomicRelative_minpoly_natDegree (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + r + 1))) :
    (minpoly (padicCyclotomicTower p (n + 1)) ζ).natDegree = p ^ r := by
  rw [← adjoin.finrank ((Algebra.IsIntegral.isIntegral (R := ℚ_[p]) ζ).tower_top),
    ← padicCyclotomicRelative_eq_adjoin p n r ζ hζ, padicCyclotomicRelative_finrank]

end PadicHodgeTheory
