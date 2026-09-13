# Mazur “ready-now” resolution

Resolution artifact for beads `hub-lsb1u.2.1`--`.2.5`, 2026-09-07.

The dependency panel's correction is binding: these five items were
statement-ready, not proof-ready.  This pass implements the two honest pieces
that fit the present Lean API, freezes the other consumer contracts, and
retires work made unnecessary by the page-level D8 correction.  It does not
claim missing modular-curve, quotient-isogeny or Néron-model infrastructure.

## 1. A5 re-wiring (`hub-lsb1u.2.1`)

`FLT/FreyCurve/Mazur.lean` now factors the proof into exactly two inputs:

```text
not IsIrreducible(E[p])
  -> Frey/ch03 bridge
  -> some E'/Q contains (Z/2)^2 x Z/p
  -> mazur_W
  -> contradiction.
```

The public theorem `FreyPackage.mazur` is therefore genuinely routed through
`mazur_W`.  The remaining `knownin1980s` is no longer unrestricted: it proves
only `mazurW_counterexample_of_reducible`, whose docstring lists the character,
local finite-flat/Tate, global-triviality and quotient/dual-isogeny obligations.
The old `Mazur_statement` remains as a compatibility declaration until the
upstream-safe PQ7 removal protocol is approved.

## 2. D7a formal immersion (`hub-lsb1u.2.2`)

Retired from the primary Mazur route.  The D8 page audit established that
Mazur 1977 III §5 uses the small fibres, torsion specialization,
unramifiedness/Herbrand and the infinite-isogeny argument; it does not use a
formal immersion.  Mathlib still has no scheme-level formal-immersion API or
the completed-local-ring/cotangent comparison needed for the optional isogeny
route.  Adding an abstract predicate that merely assumes point separation
would be circular, so no Lean declaration is added.

If the alternative isogeny route is revived, its statement boundary is:

```text
surjective map on completed local rings at x
  + two sections with the same specialization at x
  + equal images
  -> equal sections.
```

That work belongs to optional D7a/D7b, not to primary D8.

## 3. A4 torsion glue (`hub-lsb1u.2.3`)

`FLT/MazurW.lean` now proves
`fullTwoTorsion_survives_of_kernel_killed`.  Given an embedding
`(ZMod 2)^2 -> A`, a homomorphism `A -> B`, and a kernel killed by an integer
coprime to `2`, composition is again injective.  The proof compares the
additive order of a kernel difference with both `2` and `ell`; their gcd is
one.  The future odd-degree isogeny API only needs to supply the kernel bound.

## 4. A1 torsion finiteness (`hub-lsb1u.2.4`)

The bead title was wrong: A1 is not the Frey full-`2`-torsion interface.  Its
frozen statement is

```text
Set.Finite (AddCommGroup.torsion (E/Q).Point : Set (E/Q).Point).
```

No new `sorry` is warranted merely to duplicate that proposition.  A proof in
the present repository still needs either the Nagell--Lutz integral/minimal
model package or good reduction plus the formal-group specialization theorem.
This pass records the exact statement and leaves proof ownership with that
infrastructure; `Set.ncard` must not be used as a finiteness surrogate.

## 5. Small modular curves (`hub-lsb1u.2.5`)

The explicit-model audit found a material error in the previous descent plan:
`X_1(2,14)` has genus **4**, not genus 1, so it cannot be certified by a
per-curve elliptic `2`-descent.  The statement scaffold is:

| case | verified affine model | genus | proof certificate still required |
|---|---|---:|---|
| `X_1(2,10)` | `v^2 = u^3 + u^2 - u` (elliptic curve 20a2) | 1 | birational modular interpretation; `X(Q) ≅ Z/6`; all six points are cusps |
| `X_1(2,14)` | `(u^2+u)v^3 + (u^3+2u^2-u-1)v^2 + (u^3-u^2-4u-1)v - u^2-u = 0` | 4 | modular interpretation plus a genuine genus-4 rational-point argument/Kubert reduction; **not** elliptic descent |
| `X_1(11)` | `y^2 + (x^2+1)y + x = 0` (optimized); equivalently a proved birational Weierstrass model is needed | 1 | rank/torsion computation and cusp identification |
| `X_1(13)` | `y^2 + (x^3+x^2+1)y - x^2-x = 0` | 2 | Jacobian descent, Abel--Jacobi injectivity and complete cusp identification |

For every row, the Lean contract is deliberately split into: the plane curve,
its birational modular interpretation, the cusp locus, the arithmetic
rank/torsion or Jacobian certificate, and finally `X(Q) = cusps`.  Only the
last implication feeds W.  The equations alone receive no proof credit.

## Sources

- Andrew Sutherland, optimized equations for `X_1(m,mn)` and their universal
  elliptic curves: https://math.mit.edu/~drew/X1mn.html
- `X_1(2,10)` data file: https://math.mit.edu/~drew/X1/X1_2_10.txt
- `X_1(2,14)` data file: https://math.mit.edu/~drew/X1/X1_2_14.txt
- Andrew Sutherland and Mark van Hoeij, optimized `X_1(N)` equations:
  https://math.mit.edu/~drew/X1_optcurves.html
- González-Jiménez and Najman, model and rational-point data for
  `X_1(2,10)`: https://doi.org/10.1017/S0017089514000421
- Kubert, *Universal Bounds on the Torsion of Elliptic Curves*, Proc. LMS 33
  (1976), 193--237: https://doi.org/10.1112/plms/s3-33.2.193
