/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.Final
public import FLT.Assembly.PrimePowerSorting

/-!
# The FLT assembly with sorting at every three-power level

Full integral sorting supplies both the residual quotient and integral character
purity. Lifting, compatible families, and the rational torsion exclusion remain
explicit arithmetic inputs.
-/

@[expose] public section

open FLT.Assembly ThreeAdicPlan

/-- Full three-primary sorting supplies the three-adic Frobenius trace input. -/
theorem ThreeAdicPlan.threeAdicFrobeniusTrace_of_primePowerSorting
    (hsorted : PrimePowerSortedExtensionExists) : ThreeAdicFrobeniusTrace :=
  threeAdicFrobeniusTrace_of_sorted_inputs
    (sortedExtensionExists_of_primePowerSorting hsorted)
    (threeAdicCharacterPurity_of_primePowerSorting hsorted)

/-- Full three-primary sorting and the other three arithmetic inputs imply FLT. -/
theorem flt_of_primePowerSorting_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hsorted : PrimePowerSortedExtensionExists) : FermatLastTheorem :=
  flt_of_characteristicZero_inputs hmazur hlift hfamily
    (threeAdicFrobeniusTrace_of_primePowerSorting hsorted)

/-- Positive-natural FLT follows from full sorting and the other three arithmetic inputs. -/
theorem PNat.pow_add_pow_ne_pow_of_primePowerSorting_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hsorted : PrimePowerSortedExtensionExists)
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
    (flt_of_primePowerSorting_inputs hmazur hlift hfamily hsorted) x y z n hn
