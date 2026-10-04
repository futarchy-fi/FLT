# Lifting gates after W55

This wave does not remove the admission in `IsHardlyRamified.lifts`.
The new modules construct finite root models, integral splitting bases, and
an embedded divided-power hull. They do not prove characteristic-zero
existence for the HR deformation quotient.

## D1a-char0: arithmetic nonvanishing remains open

The specific ring is `Deformation.WittCoefficients.flatObject`, formed from
`hardlyArithmeticObject` by `hardlyFlatIdeal`. W54 identifies characteristic
zero with exclusion of every power of p from this ideal. Inspection of
`FlatReductionIdeal`, `HardlyRamifiedFlatQuotient`, and
`HardlyRamifiedWittLift` supplies only residual properness and effectivity
of the closed finite-flat condition, not this exclusion.

The missing input is arithmetic: for every m, an admissible finite-flat
arithmetic reduction detecting p^m, or another proof that p is not nilpotent
in the actual quotient. Nonemptiness of the residual deformation problem
does not supply compatible higher-characteristic lifts. No new equivalence
or assumed characteristic-zero point is counted as resolving this gate.
Noetherianity and the finite coefficient order remain separate obligations.

## S0a2/S0a3: finite root models constructed

`RootUniformizerModel` constructs a finite field extension and its finite
integral DVR from X^n - pi for every positive n. The degree, root equation,
uniformizer property, integral-closure property, generation, and valuation
of the base uniformizer are proved using the existing Eisenstein theorem.
A second construction embeds the integral model into a specified overfield
and sends its uniformizer to a specified root.

`TameRootIntegralModel` instantiates the latter with the exact
`tameUniformizerRoot` already used by `tameCharacter`. The root equation and
irreducibility are outputs, not extra hypotheses. This includes residue
cardinality two (root degree one).

Remaining: normality and an equivariant identification with a finite Galois
model, then the comparison for an arbitrary finite character splitting field
with its ramification exponent. A finite root model alone is not S0a3:
niveau-two, non-peu, and symmetric-power composition factors remain open.

## R1: integral splitting base and its ramification bound

`UnramifiedCharacterIntegers` uses the actual open kernel of a continuous
unramified coefficient character. Its integral closure is module finite,
has ramification index one, preserves every base uniformizer and every
nonzero natural order. Over the rational p-adic base, the order of p is
strictly less than p-1 for p>2, with the inequality proved rather than assumed.
The character need not be trivial.

Remaining: construct and descend the twisted finite-flat group scheme and
prove the prescribed generic-fiber identification. The splitting base is
an integral ring, not itself a model of the quotient representation. At p=2
the strict small-ramification inequality is unavailable (1 < 1 is false).

## Lp0: embedded divided-power hull on the actual family

`ComplexLocalizedFrobenius` extends Witt Frobenius to `ComplexAinfInvertP`
and proves Galois commutation. No power of the theta ideal maps into the
theta ideal. Thus the theta-adic construction alone does not give crystalline
Frobenius.

`ComplexLocalizedScalars` embeds the actual p-adic scalars before completion,
proves Frobenius and Galois fix them, and identifies their image in the existing
`ComplexBDeRhamPlus` with the family's previous scalar map.

`DividedPowerHull` constructs an intersection of subrings closed under actual
ambient divided powers and proves that the intersection carries a divided-power
ideal. Minimality is within this fixed ambient ring; no abstract envelope
universal property is claimed.

`ComplexDividedPowerHull` applies this construction to A_inf inside A_inf[1/p]
and the rational divided powers on the localized theta ideal. The hull has an
actual divided-power structure, factorial identities for xi, and a map into
the family's exact B_dR^+. `ComplexPDHullGalois` restricts the actual Galois
action to it and proves equivariance of that map.

Remaining: identify the hull with the required PD envelope, prove its Frobenius
stability, construct its p-adic completion and B_cris with comparison into the
exact B_dR, then tensor invariants, crystalline comparison, coefficient
naturality, and recovery of the specified integral Barsotti–Tate lattice and
all levels, including p=2. The hull is not yet named A_cris.

All new statements allow p=2 unless they explicitly assume p>2. No unavailable
Serre-weight or arbitrary-p Raynaud classification API is invoked.
