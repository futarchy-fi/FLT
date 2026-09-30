/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AbsoluteIrreducibility

/-! # The determinant of residual complex conjugation -/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

variable {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
  {k V : Type*} [Field k] [Finite k] [TopologicalSpace k] [IsTopologicalRing k]
  [Algebra ℤ_[p] k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module.Free k V] (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}

omit [Finite k] in
/-- A residual hardly ramified representation has determinant minus one at
complex conjugation, as required for an odd residual seed. -/
theorem det_complexConjugation (hρ : IsHardlyRamified hpodd hV ρ) :
    ρ.det ThreeAdicPlan.rationalComplexConjugation = -1 := by
  simpa only [ThreeAdicPlan.rationalComplexConjugation_cyclotomic, map_neg, map_one] using
    hρ.det ThreeAdicPlan.rationalComplexConjugation

end GaloisRepresentation.IsHardlyRamified
