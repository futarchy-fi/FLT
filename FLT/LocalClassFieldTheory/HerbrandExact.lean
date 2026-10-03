/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicSixTermSequence
public import FLT.LocalClassFieldTheory.SixTermCard

/-!
# Multiplicativity of the cyclic Herbrand quotient

The proved six-term sequence gives an alternating cardinal identity.
When its terms are finite, division gives the Herbrand product formula.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (S : ShortComplex (Rep k G)) (g : G) (hS : S.ShortExact)

include hS in
/-- The alternating cardinal identity of the actual periodic cohomology sequence. -/
theorem cyclicSixTerm_card :
    Nat.card ((cyclicPeriodicComplex S.X₁ g).homology false) *
      Nat.card ((cyclicPeriodicComplex S.X₃ g).homology false) *
      Nat.card ((cyclicPeriodicComplex S.X₂ g).homology true) =
    Nat.card ((cyclicPeriodicComplex S.X₂ g).homology false) *
      Nat.card ((cyclicPeriodicComplex S.X₁ g).homology true) *
      Nat.card ((cyclicPeriodicComplex S.X₃ g).homology true) :=
  sixTerm_card
    (cyclicPeriodicHomologyMap g S.f false) (cyclicPeriodicHomologyMap g S.g false)
    (cyclicPeriodicConnecting S g hS false)
    (cyclicPeriodicHomologyMap g S.f true) (cyclicPeriodicHomologyMap g S.g true)
    (cyclicPeriodicConnecting S g hS true)
    (cyclicPeriodicHomology_comp S g false)
    (cyclicPeriodicHomology_comp_connecting S g hS false)
    (cyclicPeriodicConnecting_comp S g hS false)
    (cyclicPeriodicHomology_comp S g true)
    (cyclicPeriodicHomology_comp_connecting S g hS true)
    (cyclicPeriodicConnecting_comp S g hS true)
    (cyclicSixTerm_exact_middle S g hS false) (cyclicSixTerm_exact_right S g hS false)
    (cyclicSixTerm_exact_left S g hS false) (cyclicSixTerm_exact_middle S g hS true)
    (cyclicSixTerm_exact_right S g hS true) (cyclicSixTerm_exact_left S g hS true)

/-- The Herbrand quotient defined by the two actual periodic homologies. -/
def cyclicHerbrandQuotient (A : Rep k G) : ℚ :=
  (Nat.card ((cyclicPeriodicComplex A g).homology false) : ℚ) /
    Nat.card ((cyclicPeriodicComplex A g).homology true)

include hS in
/-- Multiplicativity for a short exact coefficient sequence with finite periodic cohomology. -/
theorem cyclicHerbrandQuotient_mul
    [∀ i, Finite ((cyclicPeriodicComplex S.X₁ g).homology i)]
    [∀ i, Finite ((cyclicPeriodicComplex S.X₂ g).homology i)]
    [∀ i, Finite ((cyclicPeriodicComplex S.X₃ g).homology i)] :
    cyclicHerbrandQuotient g S.X₂ =
      cyclicHerbrandQuotient g S.X₁ * cyclicHerbrandQuotient g S.X₃ :=
  sixTerm_ratio Nat.card_pos Nat.card_pos Nat.card_pos (cyclicSixTerm_card S g hS)

/-- For cyclic G this is the usual H²/H¹ quotient. -/
theorem cyclicHerbrandQuotient_eq (A : Rep k G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cyclicHerbrandQuotient g A =
      (Nat.card (groupCohomology A 2) : ℚ) / Nat.card (groupCohomology A 1) := by
  unfold cyclicHerbrandQuotient
  rw [Nat.card_congr (cyclicPeriodicGroupEvenIso A g hg 2 (by decide)).toLinearEquiv.toEquiv.symm,
    Nat.card_congr (cyclicPeriodicGroupOddIso A g hg 1 (by decide)).toLinearEquiv.toEquiv.symm]

end LocalClassFieldTheory
