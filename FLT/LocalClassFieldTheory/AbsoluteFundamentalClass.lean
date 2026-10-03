/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AbsoluteInvariant

/-!
# Normalized absolute fundamental classes

The class of denominator n is the inverse image of positive 1/n under the
constructed local invariant. This fixes the arithmetic Frobenius convention.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  relativeBaseTower

/-- The absolute class with normalized positive invariant 1/n. -/
def absoluteFundamentalClass (n : ℕ) : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2 :=
  (absoluteInvariant R K C p).symm (↑((1 : ℚ) / n) : AddCircle (1 : ℚ))

/-- The fundamental class has the specified positive invariant. -/
theorem absoluteFundamentalClass_invariant (n : ℕ) :
    absoluteInvariant R K C p (absoluteFundamentalClass R K C p n) =
      (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) :=
  (absoluteInvariant R K C p).apply_symm_apply _

/-- The normalization characterizes the absolute class uniquely. -/
theorem absoluteFundamentalClass_eq_iff (n : ℕ)
    (x : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2) :
    x = absoluteFundamentalClass R K C p n ↔
      absoluteInvariant R K C p x = (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) := by
  rw [← absoluteFundamentalClass_invariant R K C p n]
  exact (absoluteInvariant R K C p).injective.eq_iff.symm

/-- The class of denominator n is annihilated by n. -/
theorem absoluteFundamentalClass_nsmul (n : ℕ) :
    n • absoluteFundamentalClass R K C p n = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  let : NeZero n := ⟨hn⟩
  apply (absoluteInvariant R K C p).injective
  rw [map_nsmul, map_zero, absoluteFundamentalClass_invariant]
  have he : zmodToRatCircle n 1 = (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) := by
    simpa using zmodToRatCircle_intCast n 1
  rw [← he]
  exact nsmul_zmodToRatCircle n 1

end LocalClassFieldTheory
