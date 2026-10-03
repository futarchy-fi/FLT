/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicPrincipalKernel
public import FLT.PadicHodgeTheory.ComplexThetaGenerator

/-! # The actual integral Fontaine theta kernel is principal -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- One division step by the actual candidate, with remainder still in the kernel. -/
theorem complexTheta_ker_decomposition (x : Ainf p)
    (hx : x ∈ RingHom.ker (complexTheta p)) :
    ∃ a y, y ∈ RingHom.ker (complexTheta p) ∧
      x = complexThetaGenerator p * a + p * y := by
  obtain ⟨a, ha⟩ := complexTheta_ker_coeff_dvd p x hx
  have hd : (p : Ainf p) ∣ x - complexThetaGenerator p * WittVector.teichmuller p a := by
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    change WittVector.constantCoeff
      (x - complexThetaGenerator p * WittVector.teichmuller p a) = 0
    rw [map_sub, map_mul]
    change x.coeff 0 - (complexThetaGenerator p).coeff 0 * a = 0
    rw [complexThetaGenerator_coeff_zero, ha, sub_self]
  obtain ⟨y, hy⟩ := hd
  have hyker : y ∈ RingHom.ker (complexTheta p) := by
    change complexTheta p y = 0
    have he : (p : 𝓞_ℂ_[p]) * complexTheta p y = 0 := by
      calc
        _ = complexTheta p ((p : Ainf p) * y) := by rw [map_mul, map_natCast]
        _ = complexTheta p (x - complexThetaGenerator p * WittVector.teichmuller p a) :=
          congrArg (complexTheta p) hy.symm
        _ = 0 := by
          rw [map_sub, map_mul, show complexTheta p x = 0 from hx,
            show complexTheta p (complexThetaGenerator p) = 0 from
              complexThetaGenerator_mem_ker p, zero_mul, sub_self]
    exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine ⟨WittVector.teichmuller p a, y, hyker, ?_⟩
  rw [← hy]
  ring

/-- A genuine principal generator of the theta kernel, with no generator assumption. -/
theorem complexTheta_ker_eq_span :
    RingHom.ker (complexTheta p) = Ideal.span {complexThetaGenerator p} :=
  ideal_eq_span_of_adic_decomposition (p : Ainf p) (complexThetaGenerator p)
    (RingHom.ker (complexTheta p)) (complexThetaGenerator_mem_ker p)
    (complexTheta_ker_decomposition p)

/-- Kernel membership is precisely divisibility by the constructed generator. -/
theorem complexTheta_eq_zero_iff_dvd (x : Ainf p) :
    complexTheta p x = 0 ↔ complexThetaGenerator p ∣ x := by
  rw [← RingHom.mem_ker, complexTheta_ker_eq_span, Ideal.mem_span_singleton]

end PadicHodgeTheory
