# Decision: re-base the FLT campaign at prime exponent p ≥ 17

Status: **accepted 2026-09-09** (`hub-lsb1u.12`).

## Decision

The Wiles/Mazur campaign may assume FLT for every prime exponent `p ≥ 17` and
assemble the final theorem from that result plus the already formalized small
exponents. This changes the proof decomposition, not the statement
`FermatLastTheorem`.

The finite cases below the new boundary are exactly `5`, `7`, `11`, and `13`.
The current `flt-regular` source exports closed theorems
`fermatLastTheoremFive`, `fermatLastTheoremSeven`,
`fermatLastTheoremEleven`, and `fermatLastTheoremThirteen`, as well as
`FLT_small : n ∈ Finset.Icc 3 16 → FermatLastTheoremFor n`. Its top-level
`flt_regular` theorem covers both cases of FLT for every odd regular prime.
Exponents `3` and `4` remain supplied by Mathlib.

Consequently C1–C4 in the Mazur map are not campaign proof obligations once
the external small-exponent interface is integrated. The modular-Jacobian core
still begins at `p = 17`; no classical shortcut for `17` or `19` is assumed.

## Adversarial composition check

The composition is exhaustive: the existing reduction produces a prime
`p ≥ 5`. Either `p ≥ 17`, or primality and `5 ≤ p < 17` leave exactly
`p ∈ {5, 7, 11, 13}`. Thus no exponent is lost at the boundary.

The decision does **not** use “the first irregular prime is 37” as a proof
step. That fact alone would not supply the concrete Lean terms needed for the
small cases. It also does not narrow the hard theorem to irregular primes;
doing that would require an additional regular/irregular case split and a
compatible decidable interface, for no present campaign benefit.

Changing only `FLT.Bosses.B2` would be insufficient. To realize the saving,
the `B3` and `B4` obligations and their Frey-package bridge must also be
restricted to packages with exponent at least `17`; otherwise `B3 := IsEmpty
FreyPackage` silently retains every small-prime obligation. Any Mazur/W
quantifiers used by that route must be restricted consistently.

## Integration

Implemented by `hub-lsb1u.14`. The repository still pins Lean `v4.34.0-rc1`
with Mathlib `bc06ce9f87cda9bf825ecab192b115685e629898`, while the reviewed upstream
`flt-regular` revision targets Lean `v4.34.0-rc2`. To avoid a moving or
incompatible dependency, the implementation vendors the compatibility port
from AINTLIB commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`; its
`projects/FltRegular` tree last changed at
`fa3c5e6ee266ce3060bf9964fa3a592c9f8fcd8e`. Exact provenance and licensing are
recorded in `vendor/flt-regular/README.md`.

The integration:

1. vendors the exact attributed compatibility port;
2. adds and kernel-checks the small-exponent/`p ≥ 17` assembly bridge;
3. re-quantifies B2, B3, B4, the Frey-package bridge, and the consumed Mazur/W
   statement together;
4. introduces no new `sorry` and regression-checks that the imported small
   theorem and the final assembly bridge contain neither `sorryAx` nor
   `knownin1980s`.

The source-level B2/B3/B4 and consumed Mazur/W path now all begin at `p ≥ 17`.
The more general Frey-package constructor remains available at `p ≥ 5`, but its
new exponent-preserving result lets the B3 bridge retain the large-prime bound.

## Evidence reviewed

- Best–Birkbeck–Brasca–Rodriguez Boidi–van de Velde–Yang,
  [*A complete formalization of Fermat's Last Theorem for regular primes in
  Lean*](https://arxiv.org/abs/2410.01466), covering both FLT cases.
- [`FltRegular/FltRegular.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/FltRegular.lean),
  exporting `flt_regular`.
- [`FltRegular/SmallNumbers/SmallNumbers.lean`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/SmallNumbers/SmallNumbers.lean),
  assembling `FLT_small` from the concrete theorems for `5`, `7`, `11`, and
  `13`.
