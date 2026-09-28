/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.Proof
public import FLT.Assembly.ThreeAdicTrace

/-!
# The FLT assembly with the three-adic inputs expanded

The three-adic trace statement is proved from integral sorting and rank-one
character purity. Together with lifting, compatible families, and the rational
torsion exclusion, these give the positive-natural statement.
-/

@[expose] public section

open FLT.Assembly ThreeAdicPlan

/-- The five remaining arithmetic inputs imply Fermat's Last Theorem. -/
theorem flt_of_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hsorted : SortedExtensionExists) (hpurity : ThreeAdicCharacterPurity) :
    FermatLastTheorem :=
  flt_of_characteristicZero_inputs hmazur hlift hfamily
    (threeAdicFrobeniusTrace_of_sorted_inputs hsorted hpurity)

/-- The positive-natural form of Fermat's Last Theorem from the five remaining inputs. -/
theorem PNat.pow_add_pow_ne_pow_of_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hsorted : SortedExtensionExists) (hpurity : ThreeAdicCharacterPurity)
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
    (flt_of_inputs hmazur hlift hfamily hsorted hpurity) x y z n hn
