/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.FreyIrreducibility
public import FLT.Assembly.SmallRegularPrimes
public import FLT.Proof

/-!
# Fermat's Last Theorem from the Frey-only irreducibility input

Small exponents use the regular-prime proofs. At primes at least seventeen,
only the two conflicting statements about the Frey representation enter.
-/

@[expose] public section

namespace FLT.Assembly

/-- Frey irreducibility and reducibility rule out only large-prime packages. -/
theorem no_large_freyPackage (hirred : FreyIrreducibility)
    (hred : FLT.Bosses.B4) (P : FreyPackage) (hp17 : 17 ≤ P.p) : False :=
  hred P hp17 (hirred P hp17)

/-- The Frey-only input suffices after the regular primes have been discharged. -/
theorem flt_of_freyIrreducibility (hirred : FreyIrreducibility)
    (hred : FLT.Bosses.B4) : FermatLastTheorem :=
  flt_of_prime_ge_seventeen
    (FreyPackage.fermatLastTheoremFor_p_ge_17 (no_large_freyPackage hirred hred))

/-- Positive-natural FLT with the narrowly scoped Frey input. -/
theorem pow_add_pow_ne_pow_of_freyIrreducibility (hirred : FreyIrreducibility)
    (hred : FLT.Bosses.B4) (x y z : ℕ+) (n : ℕ) (hn : n > 2) :
    x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
    (flt_of_freyIrreducibility hirred hred) x y z n hn

end FLT.Assembly
