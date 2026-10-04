/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicIrreducible
public import FLT.PadicHodgeTheory.PadicCyclotomicTower

/-! # Exact degrees of the actual local cyclotomic tower -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- A primitive p-power root has the full cyclotomic minimal polynomial over Q_p. -/
theorem padicCyclotomic_minpoly (s : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (s + 1))) :
    minpoly ℚ_[p] ζ = Polynomial.cyclotomic (p ^ (s + 1)) ℚ_[p] :=
  (hζ.minpoly_eq_cyclotomic_of_irreducible (padic_cyclotomic_primePower_irreducible p s)).symm

/-- The actual p^(s+1)-th cyclotomic field has degree p^s times (p-1). -/
theorem padicCyclotomicTower_finrank (s : ℕ) :
    Module.finrank ℚ_[p] (padicCyclotomicTower p (s + 1)) = p ^ s * (p - 1) := by
  let : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [IsCyclotomicExtension.finrank (n := p ^ (s + 1)) (padicCyclotomicTower p (s + 1))
    (padic_cyclotomic_primePower_irreducible p s), Nat.totient_prime_pow hp.out (by omega),
    Nat.add_sub_cancel]

/-- After the first level, every transition strictly increases the actual field. -/
theorem padicCyclotomicTower_strict_succ (s : ℕ) :
    padicCyclotomicTower p (s + 1) < padicCyclotomicTower p (s + 2) := by
  refine lt_of_le_of_ne (padicCyclotomicTower_mono p (by omega)) ?_
  intro he
  have hd := congrArg (fun E : IntermediateField ℚ_[p] (PadicAlgCl p) ↦
    Module.finrank ℚ_[p] E) he
  rw [padicCyclotomicTower_finrank p s, padicCyclotomicTower_finrank p (s + 1),
    pow_succ'] at hd
  have hpow : 0 < p ^ s := pow_pos hp.out.pos _
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hlt : p ^ s * (p - 1) < p * (p ^ s * (p - 1)) :=
    lt_mul_of_one_lt_left (Nat.mul_pos hpow hp1) hp.out.one_lt
  exact (ne_of_lt hlt) (by simpa only [Nat.mul_assoc] using hd)

end PadicHodgeTheory
