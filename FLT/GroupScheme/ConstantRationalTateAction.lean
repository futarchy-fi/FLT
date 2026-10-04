/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalTateVectors

/-! # Trivial original Galois action on the constant etale Tate module -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ConstantRationalPower
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Every actual Tate vector in the constant system is fixed by the original local Galois group. -/
theorem tate_galois_fixed (σ : Field.absoluteGaloisGroup K) (x : (system p hp).tateSequences) :
    σ • x = x := by
  apply (system p hp).tate_ext
  intro n
  exact constantGroupModel_smul _ _ _ σ (x.val n)

/-- The chosen compatible generator is nonzero already at the first positive level. -/
theorem generator_ne_zero : generator p hp ≠ 0 := by
  intro he
  have h := congrArg ((system p hp).tateEval 1) he
  change points p 1 (Ideal.Quotient.mk _ 1) = 0 at h
  rw [(points p 1).map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, pow_one] at h
  have hd : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one h)
  rcases hd with hd | hd <;> omega

end ThreeAdicPlan.ConstantRationalPower
