/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialFlat
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialPolynomial
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialRamification

/-! # The standard integral member is hardly ramified -/

@[expose] public noncomputable section
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime]

/-- All four clauses hold for the actual standard integral representation. -/
theorem cyclotomicTrivial_hardlyRamified (hp : Odd p) :
    IsHardlyRamified hp (cyclotomicTrivial_rank p) (cyclotomicTrivial p) where
  det g := cyclotomicTrivial_det p g
  isUnramified q hq hgood := cyclotomicTrivial_unramified p q hq hgood.2
  isFlat := cyclotomicTrivial_isFlatAt p _
  isTameAtTwo := cyclotomicTrivial_tameAtTwo p

end GaloisRepresentation
