/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegralThickening

/-! # Compatibility and nilpotence of integral precision reductions -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- All rectangular precision reductions compose on the original representatives. -/
theorem complexThickeningReduce_comp {r₀ r₁ r₂ s₀ s₁ s₂ : ℕ}
    (hr : r₀ ≤ r₁) (hr' : r₁ ≤ r₂) (hs : s₀ ≤ s₁) (hs' : s₁ ≤ s₂) :
    (complexThickeningReduce p hr hs).comp (complexThickeningReduce p hr' hs') =
      complexThickeningReduce p (hr.trans hr') (hs.trans hs') :=
  Ideal.Quotient.factor_comp _ _

/-- The full kernel of a precision reduction is the image of the lower precision ideal. -/
theorem complexThickeningReduce_ker {r r' s s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    RingHom.ker (complexThickeningReduce p hr hs) =
      (complexThickeningIdeal p r s).map (Ideal.Quotient.mk (complexThickeningIdeal p r' s')) :=
  integralFactor_ker _

/-- Every reduction between positive precisions has a nilpotent kernel. -/
theorem complexThickeningReduce_ker_nilpotent {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (hr₀ : 0 < r) (hs₀ : 0 < s) :
    IsNilpotent (RingHom.ker (complexThickeningReduce p hr hs)) := by
  refine ⟨r' + s', integralFactor_ker_pow _ _ ?_⟩
  change (RingHom.ker (complexTheta p) ^ r ⊔ Ideal.span {(p : Ainf p) ^ s}) ^
    (r' + s') ≤ _
  apply Ideal.sup_pow_add_le_pow_sup_pow.trans
  apply sup_le_sup
  · rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by nlinarith)
  · rw [← Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right (by nlinarith)

/-- One theta step at positive order is a square-zero extension. -/
theorem complexThickeningReduce_theta_squareZero (r s : ℕ) (hr : 0 < r) :
    RingHom.ker (complexThickeningReduce p (Nat.le_succ r) (le_refl s)) ^ 2 = ⊥ := by
  rw [complexThickeningReduce_ker]
  have hz : (Ideal.span {(p : Ainf p) ^ s}).map
      (Ideal.Quotient.mk (complexThickeningIdeal p (r + 1) s)) = ⊥ :=
    Ideal.map_mk_eq_bot_of_le le_sup_right
  change ((RingHom.ker (complexTheta p) ^ r ⊔ Ideal.span {(p : Ainf p) ^ s}).map _) ^ 2 = _
  rw [Ideal.map_sup, hz, sup_bot_eq, ← Ideal.map_pow, ← pow_mul]
  exact Ideal.map_mk_eq_bot_of_le ((Ideal.pow_le_pow_right (by nlinarith)).trans le_sup_left)

/-- One positive p-precision step is also square-zero, with theta order held fixed. -/
theorem complexThickeningReduce_prime_squareZero (r s : ℕ) (hs : 0 < s) :
    RingHom.ker (complexThickeningReduce p (le_refl r) (Nat.le_succ s)) ^ 2 = ⊥ := by
  rw [complexThickeningReduce_ker]
  have hz : (RingHom.ker (complexTheta p) ^ r).map
      (Ideal.Quotient.mk (complexThickeningIdeal p r (s + 1))) = ⊥ :=
    Ideal.map_mk_eq_bot_of_le le_sup_left
  change ((RingHom.ker (complexTheta p) ^ r ⊔ Ideal.span {(p : Ainf p) ^ s}).map _) ^ 2 = _
  rw [Ideal.map_sup, hz, bot_sup_eq, ← Ideal.map_pow]
  apply Ideal.map_mk_eq_bot_of_le
  apply le_trans _ le_sup_right
  rw [← Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right (by nlinarith)

/-- Reduction on the actual residue coefficient rings. -/
def complexIntegerModPowReduce {s s' : ℕ} (hs : s ≤ s') :
    ComplexIntegerModPow p s' →+* ComplexIntegerModPow p s :=
  Ideal.Quotient.factor (by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right hs)

/-- Theta commutes with both precision directions. -/
theorem complexThickeningTheta_reduce {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (hr₀ : 0 < r) :
    (complexThickeningTheta p r s hr₀).comp (complexThickeningReduce p hr hs) =
      (complexIntegerModPowReduce p hs).comp
        (complexThickeningTheta p r' s' (hr₀.trans_le hr)) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end PadicHodgeTheory
