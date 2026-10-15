/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalFactorReduction
public import FLT.Mazur.WeierstrassDilatationCoefficients

/-!
# The standard terminal punctures lie in the original horizontal open

At a prime containing x, the divided cubic forces y to vanish modulo the
nilpotent coefficient ideal. Both complete corrected node factors then vanish.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  {S : Type*} [CommRing S] [Algebra R S]
  (g : Coordinate W s b3 b4 b6 →ₐ[R] S) (P : Ideal S) [P.IsPrime]
local notation "f" => algebraMap R S
local notation "u" => g (x W s b3 b4 b6)
local notation "v" => g (y W s b3 b4 b6)

/-- On the original cubic, a prime containing x, b3 and b6 also contains y. -/
theorem ordinate_mem_of_abscissa_mem (hx : u ∈ P) (h3 : f b3 ∈ P) (h6 : f b6 ∈ P) :
    v ∈ P := by
  have he := congrArg (Ideal.Quotient.mk P) (equation_map W s b3 b4 b6 g)
  have hx₀ := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have h3₀ := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have h6₀ := Ideal.Quotient.eq_zero_iff_mem.mpr h6
  simp only [map_add, map_mul, map_pow, hx₀, h3₀, h6₀, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero he)

variable (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (ha : IsUnit W.a₁) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "J" => I.map f

include hI in
/-- Every prime contains the full extension of a nilpotent coefficient ideal. -/
theorem terminalCoefficientIdeal_le_prime : J ≤ P := by
  obtain ⟨N, hN⟩ := NilpotentPolynomialInverse.mapIdeal_nilpotent I hI f
  exact Ideal.IsPrime.le_of_pow_le (hN.le.trans bot_le)

include h3 in
/-- The first full corrected factor vanishes at every prime outside the original horizontal open. -/
theorem terminalNodeSmall_mem_of_x_mem (hx : u ∈ P) :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) ∈ P := by
  have hJ := terminalCoefficientIdeal_le_prime P I hI
  have hy := ordinate_mem_of_abscissa_mem W s b3 b4 b6 g P hx
    (hJ (Ideal.mem_map_of_mem f h3)) (hJ (Ideal.mem_map_of_mem f h6))
  have ht := hJ (terminalNodeSmall_sub_y_mem W s b3 b4 b6 r I hI hrI ha h4 h6 g)
  simpa only [sub_add_cancel] using P.add_mem ht hy

include h3 in
/-- The opposite corrected factor also vanishes outside the original horizontal open. -/
theorem terminalNodeOpposite_mem_of_x_mem (hx : u ∈ P) :
    g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) ∈ P := by
  have hJ := terminalCoefficientIdeal_le_prime P I hI
  have hy := ordinate_mem_of_abscissa_mem W s b3 b4 b6 g P hx
    (hJ (Ideal.mem_map_of_mem f h3)) (hJ (Ideal.mem_map_of_mem f h6))
  have ht := hJ (terminalNodeOpposite_sub_tangent_mem W s b3 b4 b6 r I hI hrI ha h4 h6 g h3)
  simpa only [sub_add_cancel] using P.add_mem ht (P.add_mem hy (P.mul_mem_right (f W.a₁) hx))

variable (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
local notation "e" => terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6 hr

include h3 in
/-- Either standard node puncture is contained in the original horizontal open. -/
theorem terminalNodePuncture_horizontal
    (P₀ : Ideal (NodalFiber.Coordinate c)) [P₀.IsPrime] (opposite : Bool)
    (hp : (if opposite then NodalFiber.p c else NodalFiber.q c) ∉ P₀) :
    e (x W s b3 b4 b6) ∉ P₀ := by
  intro hx
  apply hp
  cases opposite
  · have h := terminalNodeOpposite_mem_of_x_mem W s b3 b4 b6 (e).toAlgHom P₀
      r I hI hrI ha h3 h4 h6 hx
    rw [← terminalNodeEquiv_symm_q W s b3 b4 b6 r I hI hrI ha h4 h6 hr] at h
    exact (e).apply_symm_apply (NodalFiber.q c) ▸ h
  · have h := terminalNodeSmall_mem_of_x_mem W s b3 b4 b6 (e).toAlgHom P₀
      r I hI hrI ha h3 h4 h6 hx
    rw [← terminalNodeEquiv_symm_p W s b3 b4 b6 r I hI hrI ha h4 h6 hr] at h
    exact (e).apply_symm_apply (NodalFiber.p c) ▸ h

end FLT.Mazur.WeierstrassDilatation
