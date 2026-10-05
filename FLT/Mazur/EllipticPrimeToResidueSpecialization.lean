/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalValuation

/-!
# Prime-to-residue torsion and actual smooth reduction

On the smooth-reduction subgroup of an integral Weierstrass equation, reduction
is injective on torsion of order prime to the residue characteristic. The local
ring need not be unramified, and residue characteristic two is included.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- A prime-to-residue torsion point in the smooth reduction kernel is zero. -/
theorem smoothReductionHom_torsion_eq_zero_of_not_dvd
    (p n : ℕ) [CharP (ResidueField A) p] (hn : ¬ p ∣ n)
    (P : ellipticE0 A W) (hP : n • P = 0) (hred : smoothReductionHom A W P = 0) : P = 0 := by
  have hmem : P.val ∈ ellipticE1 A W := (mem_smoothReductionHom_ker_iff A W P).mp hred
  let Q : ellipticE1 A W := ⟨P.val, hmem⟩
  have hQ : n • Q = 0 := Subtype.ext (congrArg (fun R : ellipticE0 A W => R.val) hP)
  have hz := (ellipticE1_nsmul_eq_zero_iff_of_not_dvd A W p n hn Q).mp hQ
  exact Subtype.ext (congrArg (fun R : ellipticE1 A W => R.val) hz)

/-- Reduction is injective on prime-to-residue n-torsion, also at two and over ramified rings. -/
theorem smoothReductionHom_injOn_torsion_of_not_dvd
    (p n : ℕ) [CharP (ResidueField A) p] (hn : ¬ p ∣ n) :
    Set.InjOn (smoothReductionHom A W) {P | n • P = 0} := by
  intro P hP Q hQ hred
  apply sub_eq_zero.mp
  apply smoothReductionHom_torsion_eq_zero_of_not_dvd A W p n hn (P - Q)
  · rw [nsmul_sub, hP, hQ, sub_self]
  · rw [map_sub, hred, sub_self]

end FLT.Mazur
