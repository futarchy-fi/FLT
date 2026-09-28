/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.Mazur
public import FLT.Assembly.PrimeField
public import FLT.Proof

/-!
# Conditional assembly of Fermat's Last Theorem

The proved Frey-curve constructions and prime-field reductions connect the
remaining rational torsion and characteristic-zero inputs to the traditional
positive-natural statement.
-/

@[expose] public section

open FLT.Assembly GaloisRepresentation

namespace FLT.Bosses

/-- The characteristic-zero inputs give reducibility of Frey torsion. -/
theorem B4_of_inputs
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hthree : ThreeAdicFrobeniusTrace) : B4 := by
  intro P _
  let instPrime : Fact P.p.Prime := ⟨P.pp⟩
  exact IsHardlyRamified.not_isIrreducible_of_inputs hlift hfamily hthree
    P.p P.hp5 P.hp_odd _ (FreyCurve.torsion_rank P)
    (P.freyCurve.galoisRep P.p P.hppos) (FreyCurve.torsion_isHardlyRamified P)

/-- The explicit torsion exclusion turns Frey reducibility into nonexistence. -/
theorem B3_of_torsionExclusion
    (hmazur : MazurTorsionExclusion) (hB4 : B4) : B3 := by
  intro P hp17
  exact hB4 P hp17 (P.mazur_of_torsionExclusion hmazur hp17)

end FLT.Bosses

/-- The rational torsion and characteristic-zero inputs imply Fermat's Last Theorem. -/
theorem flt_of_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hthree : ThreeAdicFrobeniusTrace) : FermatLastTheorem :=
  FLT.Bosses.B2_implies_B1 (FLT.Bosses.B3_implies_B2
    (FLT.Bosses.B3_of_torsionExclusion hmazur (FLT.Bosses.B4_of_inputs hlift hfamily hthree)))

/-- The positive-natural form of Fermat's Last Theorem from the four remaining inputs. -/
theorem PNat.pow_add_pow_ne_pow_of_inputs
    (hmazur : MazurTorsionExclusion)
    (hlift : HardlyRamifiedLifting) (hfamily : HardlyRamifiedCompatibleFamilies)
    (hthree : ThreeAdicFrobeniusTrace)
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
    (flt_of_inputs hmazur hlift hfamily hthree) x y z n hn
