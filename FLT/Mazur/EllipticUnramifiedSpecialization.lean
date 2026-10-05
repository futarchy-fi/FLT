/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticUnramifiedKernel

/-!
# Actual smooth reduction on unramified elliptic torsion

The proven E₁ bounds control the kernel of the actual E₀ reduction homomorphism.
They give injectivity on n-torsion at odd unramified primes, including n divisible
by the residue characteristic. At two, equal reductions of torsion points imply
equal doubles. No Néron model or abelian-scheme specialization is asserted.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]
variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]

/-- A torsion point of E₀ reducing to zero vanishes at an odd unramified prime. -/
theorem smoothReductionHom_torsion_eq_zero_unramified_odd (hp2 : p ≠ 2)
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : A) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE0 A W) (hP : n • P = 0)
    (hred : smoothReductionHom A W P = 0) : P = 0 := by
  have hmem : P.val ∈ ellipticE1 A W := (mem_smoothReductionHom_ker_iff A W P).mp hred
  let Q : ellipticE1 A W := ⟨P.val, hmem⟩
  have hQ : n • Q = 0 := Subtype.ext (congrArg (fun R : ellipticE0 A W => R.val) hP)
  have hz := (ellipticE1_nsmul_eq_zero_iff_unramified_odd A W p hp2 hm hp0 n hn Q).mp hQ
  exact Subtype.ext (congrArg (fun R : ellipticE1 A W => R.val) hz)

/-- Smooth reduction is injective on actual n-torsion at an odd unramified prime. -/
theorem smoothReductionHom_injOn_torsion_unramified_odd (hp2 : p ≠ 2)
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : A) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    Set.InjOn (smoothReductionHom A W) {P | n • P = 0} := by
  intro P hP Q hQ hred
  apply sub_eq_zero.mp
  apply smoothReductionHom_torsion_eq_zero_unramified_odd A W p hp2 hm hp0 n hn (P - Q)
  · rw [nsmul_sub, hP, hQ, sub_self]
  · rw [map_sub, hred, sub_self]

/-- At any unramified prime, the torsion kernel of smooth reduction is killed by p. -/
theorem smoothReductionHom_prime_nsmul_eq_zero_of_torsion
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : K) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE0 A W) (hP : n • P = 0)
    (hred : smoothReductionHom A W P = 0) : p • P = 0 := by
  have hmem : P.val ∈ ellipticE1 A W := (mem_smoothReductionHom_ker_iff A W P).mp hred
  let Q : ellipticE1 A W := ⟨P.val, hmem⟩
  have hQ : n • Q = 0 := Subtype.ext (congrArg (fun R : ellipticE0 A W => R.val) hP)
  have hz := ellipticE1_nsmul_eq_zero_of_torsion_unramified A W p hm hp0 n hn Q hQ
  exact Subtype.ext (congrArg (fun R : ellipticE1 A W => R.val) hz)

/-- Equal reductions of n-torsion points give equal p-multiples, also at two. -/
theorem smoothReductionHom_eq_imp_prime_nsmul_eq
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : K) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (P Q : ellipticE0 A W) (hP : n • P = 0) (hQ : n • Q = 0)
    (hred : smoothReductionHom A W P = smoothReductionHom A W Q) : p • P = p • Q := by
  apply sub_eq_zero.mp
  rw [← nsmul_sub]
  apply smoothReductionHom_prime_nsmul_eq_zero_of_torsion A W p hm hp0 n hn (P - Q)
  · rw [nsmul_sub, hP, hQ, sub_self]
  · rw [map_sub, hred, sub_self]

end FLT.Mazur
