/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.HeckeEigenCoefficients
import Mathlib.Algebra.Field.ZMod
import Lean

/-! # Trust audit for the first-coefficient step of Mazur's Proposition 3.1 -/

open Lean Elab Command

run_elab do
  for n in #[``FLT.Mazur.eq_zero_of_hecke_relations,
      ``FLT.Mazur.coeff_one_ne_zero_of_hecke_relations,
      ``FLT.Mazur.exists_coeff_one_ne_zero_of_hecke_action,
      ``FLT.Mazur.coeff_one_surjective_of_hecke_action] do
    for a in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {n}"

-- The intended residue characteristic is allowed, including primes l = 3
-- in the T relations. No division by l or characteristic-zero instance is used.
example (f : PowerSeries (ZMod 3)) (c : ℕ → ZMod 3)
    (hf : f ≠ 0) (hzero : f.coeff 0 = 0)
    (hU : ∀ m, f.coeff (17 * m) = c 17 * f.coeff m)
    (hT : ∀ l, l.Prime → l ≠ 17 → ∀ m,
      f.coeff (l * m) = c l * f.coeff m -
        if l ∣ m then (l : ZMod 3) * f.coeff (m / l) else 0) :
    f.coeff 1 ≠ 0 :=
  FLT.Mazur.coeff_one_ne_zero_of_hecke_relations f c 17 hf hzero hU hT

