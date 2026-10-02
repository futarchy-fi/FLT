/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.EllipticCurve.SmallResidueTorsion
import Mathlib.Algebra.Field.ZMod
import Lean

/-! # Small-residue torsion: trust audit and residue-characteristic regressions -/

open Lean Elab Command

run_elab do
  for n in #[``WeierstrassCurve.card_point_le_coordinates,
      ``WeierstrassCurve.eq_zero_of_prime_nsmul_of_card_lt,
      ``WeierstrassCurve.reducePoint_eq_zero_of_large_prime,
      ``WeierstrassCurve.eq_zero_of_reducePoint_eq_zero_of_unit_nsmul,
      ``WeierstrassCurve.eq_zero_of_large_prime_small_residue,
      ``WeierstrassCurve.no_large_prime_torsion_of_small_residue] do
    for a in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {n}"

example : let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    ∀ (E : WeierstrassCurve (ZMod 2)) (P : E.toAffine.Point),
      17 • P = 0 → P = 0 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro _ E P h
  exact E.eq_zero_of_prime_nsmul_of_card_lt (by decide) (by norm_num) P h

example : let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    ∀ (E : WeierstrassCurve (ZMod 3)) (P : E.toAffine.Point),
      17 • P = 0 → P = 0 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro _ E P h
  exact E.eq_zero_of_prime_nsmul_of_card_lt (by decide) (by norm_num) P h
