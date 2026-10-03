/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFontaineTheta

/-! # Divisibility in the actual tilt from compatible integral roots -/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Divisibility at coordinate zero propagates to every compatible root. -/
theorem complexRootSequence_coeff_dvd (a b : Perfection 𝓞_ℂ_[p] p)
    (h : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a ∣
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b) (n : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a ∣ Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b := by
  rw [(PadicComplexInt.integers p).dvd_iff_le] at h ⊢
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
  simpa only [← Valuation.map_pow, ← map_pow (algebraMap 𝓞_ℂ_[p] ℂ_[p]),
    Perfection.coeffMonoidHom_pow_p_pow_self] using h

/-- A nonzero zeroth coordinate forces every root coordinate to be nonzero. -/
theorem complexRootSequence_coeff_ne_zero (a : Perfection 𝓞_ℂ_[p] p)
    (h : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a ≠ 0) (n : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a ≠ 0 := by
  intro hn
  have hp := Perfection.coeffMonoidHom_pow_p_pow_self a n
  rw [hn, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at hp
  exact h hp.symm

/-- Coordinatewise integral quotients themselves form a compatible root sequence. -/
theorem complexRootSequence_dvd (a b : Perfection 𝓞_ℂ_[p] p)
    (ha : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a ≠ 0)
    (h : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a ∣
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b) : a ∣ b := by
  choose c hc using complexRootSequence_coeff_dvd p a b h
  have hcompat (n : ℕ) : c (n + 1) ^ p = c n := by
    apply mul_left_cancel₀ (complexRootSequence_coeff_ne_zero p a ha n)
    calc
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a * c (n + 1) ^ p =
          (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p (n + 1) a * c (n + 1)) ^ p := by
        rw [mul_pow, Perfection.coeffMonoidHom_pow_p']
      _ = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b := by
        rw [← hc, Perfection.coeffMonoidHom_pow_p']
      _ = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a * c n := hc n
  refine ⟨⟨c, hcompat⟩, ?_⟩
  apply Perfection.extMonoid
  intro n
  exact hc n

/-- Away from zero, divisibility of sharp values implies divisibility in the tilt. -/
theorem complexTilt_dvd_of_sharp_dvd (a b : IntegralTilt p)
    (ha : complexSharp p a ≠ 0) (h : complexSharp p a ∣ complexSharp p b) : a ∣ b := by
  let e := Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})
  have hc (x : IntegralTilt p) :
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (e.symm x) = complexSharp p x :=
    Perfection.coeff_zero_symm_quotientMulEquiv x
  obtain ⟨c, hc'⟩ := complexRootSequence_dvd p (e.symm a) (e.symm b)
    (by rwa [hc]) (by rwa [hc, hc])
  refine ⟨e c, ?_⟩
  have he := congrArg e hc'
  rw [map_mul] at he
  exact (e.apply_symm_apply b).symm.trans
    (he.trans (congrArg (fun z ↦ z * e c) (e.apply_symm_apply a)))

end PadicHodgeTheory
