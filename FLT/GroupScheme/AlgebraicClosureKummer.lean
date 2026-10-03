/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ContinuousKummerClass
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Kummer comparison over an algebraic closure of a perfect field

Algebraic closedness supplies roots; perfectness makes the algebraic
closure Galois. In particular this applies to characteristic-zero local
fields, without assuming a root-existence witness from the caller.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {n : ℕ} [NeZero n]

/-- All base-field units have nth roots in an algebraically closed extension. -/
theorem exists_unit_root (q : Kˣ) : ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L) q := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K L (q : K)) (NeZero.pos n)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne n)] at hb
    exact (map_ne_zero (algebraMap K L)).mpr q.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩

variable (K) [PerfectField K] (n)

/-- The algebraic closure of a perfect field is Galois. -/
theorem algebraicClosure_isGalois : IsGalois K (AlgebraicClosure K) := ⟨⟩

/-- The continuous Kummer equivalence over the algebraic closure of a perfect field. -/
noncomputable def algebraicClosureKummerEquiv :
    PowerClass K n ≃
      ContinuousClass Gal(AlgebraicClosure K/K) (RootModule (AlgebraicClosure K) n) := by
  letI := algebraicClosure_isGalois K
  exact continuousKummerEquiv (exists_unit_root (L := AlgebraicClosure K))

end KummerTheory
