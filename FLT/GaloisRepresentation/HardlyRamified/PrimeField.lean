/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.Topology.Instances.ZMod

/-!
# Reducibility over prime fields

This is the generic B5 input for the Frey-curve reduction of Fermat's Last Theorem.
The arithmetic argument proving this input remains open.
-/

@[expose] public section

namespace GaloisRepresentation

/-- The natural p-adic algebra structure on the prime field. -/
noncomputable local instance primeFieldPadicAlgebra (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- A hardly ramified two-dimensional representation over a prime field of
characteristic at least five is not irreducible. This is the generic B5 input;
it makes no assumption that the representation comes from a Frey curve. -/
theorem IsHardlyRamified.not_isIrreducible_of_prime_field
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hpodd : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] [Module.Free (ZMod p) V]
    (hV : Module.rank (ZMod p) V = 2) (ρ : GaloisRep ℚ (ZMod p) V)
    (hρ : IsHardlyRamified hpodd hV ρ) : ¬ ρ.IsIrreducible :=
  sorry

end GaloisRepresentation
