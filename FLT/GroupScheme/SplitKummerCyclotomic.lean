/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SplitKummerPointLaw
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The cyclotomic action on the actual split Kummer points

The root coordinate transforms by the finite residue of the local p-adic
cyclotomic character. The component coordinate is fixed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- A unit root transforms by the residue of the local cyclotomic character. -/
theorem splitKummer_root_cyclotomic
    (g : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
    (z : (AlgebraicClosure ℚ_[p])ˣ) (hz : z ^ (p ^ n) = 1) :
    Units.map g.toRingEquiv.toMonoidHom z =
      z ^ (PadicInt.toZModPow n
        (cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p g.toRingEquiv).val).val := by
  apply Units.ext
  exact cyclotomicCharacter.spec p g.toRingEquiv (z : AlgebraicClosure ℚ_[p])
    (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hz)

/-- The geometric action is cyclotomic on roots and trivial on components. -/
theorem splitKummerCoordinates_smul_cyclotomic
    (g : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
    (x : (splitKummerModel p n).Points) :
    (splitKummerCoordinates p n (g • x)).val =
      ((splitKummerCoordinates p n x).val.1,
        (splitKummerCoordinates p n x).val.2 ^ (PadicInt.toZModPow n
          (cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p g.toRingEquiv).val).val) := by
  rw [splitKummerCoordinates_smul,
    splitKummer_root_cyclotomic p n g _ (splitKummerCoordinates p n x).property]

end ThreeAdicPlan
