/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDividedCharacterAverage
public import FLT.GroupScheme.RaynaudCharacterConstantBaseChange

/-!
# The prime quotient of a fundamental universal constant

Evaluate the divided formal average on the actual lifted character. Its
image in the characteristic-p coefficient algebra is -1.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F]
  (χ : Fˣ →* Rˣ) (e : F →+* S)

/-- Extension by zero reduces to the field embedding when the unit characters agree. -/
theorem value_map_embedding (he : ∀ u : Fˣ, algebraMap R S (χ u) = e u) (a : F) :
    algebraMap R S (value χ a) = e a := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp only [value, dite_eq_right ha, he, Units.val_mk0]

/-- Evaluating a lifted character reduces to additive evaluation of its residue embedding. -/
theorem evaluate_map_embedding (he : ∀ u : Fˣ, algebraMap R S (χ u) = e u)
    (x : AddMonoidAlgebra R F) :
    algebraMap R S (evaluate (value χ) x) = additiveEvaluation e.toAddMonoidHom x := by
  induction x using AddMonoidAlgebra.induction_on with
  | of a =>
    change algebraMap R S (evaluate (value χ) (AddMonoidAlgebra.single a 1)) = _
    simpa [evaluate] using value_map_embedding χ e he a
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx =>
    rw [(evaluate (value χ)).map_smul, (additiveEvaluation e.toAddMonoidHom).map_smul]
    rw [smul_eq_mul, map_mul, hx, Algebra.smul_def]

variable [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)]
  (p : ℕ) [Fact p.Prime] [CharP F p] [CharP S p]

/-- The fundamental p-fold constant is p times an element whose residue is -1. -/
theorem exists_prime_quotient (he : ∀ u : Fˣ, algebraMap R S (χ u) = e u) :
    ∃ u : R, constant χ (χ ^ p) p = (p : R) * u ∧ algebraMap R S u = -1 := by
  obtain ⟨z, hz, hez⟩ := formalAverage_dividedPower p χ e he
  refine ⟨evaluate (value (χ ^ p)) z, ?_, ?_⟩
  · rw [constant_eq_formalAverage, hz, map_smul, smul_eq_mul]
  · rw [evaluate_map_embedding (χ ^ p) ((frobenius S p).comp e)]
    · exact hez
    · intro a
      change algebraMap R S ((χ a : R) ^ p) = e a ^ p
      rw [map_pow, he]

end ThreeAdicPlan.CharacterAverage
