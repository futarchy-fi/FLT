/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Assembly.PrimePowerFinal
public import FLT.Assembly.PrimePowerSortingProof

/-!
# Fermat's Last Theorem from three arithmetic inputs

Unconditional integral sorting discharges the sorting input in the final
assembly. Rational torsion exclusion, lifting, and compatible families remain
the three explicit arithmetic inputs.
-/

@[expose] public section

open FLT.Assembly ThreeAdicPlan

/-- Positive-natural FLT follows from the three remaining arithmetic inputs. -/
theorem PNat.pow_add_pow_ne_pow_of_three_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_primePowerSorting_inputs hmazur hlift hfamily
    primePowerSortedExtensionExists x y z n hn
