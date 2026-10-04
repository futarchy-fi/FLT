# Lifting gates after W49

Validation receipts and a read-only check are in untracked `Scratch/LiftsW49/`.
`check.py` checks source hashes, declaration axiom audits, per-module build and
lint receipts, caps, sorted imports, merge ancestry and the final root build.
The untracked `LIFTS_W49_RESULT.md` records the checked commit and timestamp.

## R1a2/R1b3: integral rigidity and the actual constant quotient

`LocalModelIdentification` derives a unique integral Hopf isomorphism from a
specified generic equivalence between p-killed models over a number-field local
completion. Its arithmetic hypotheses are adic completeness, residue
characteristic p and the explicit bound `order(p) < p - 1`. The source alone
needs an annihilation proof; the target inherits it through the equivalence.
The coefficient-field corollary applies to fields of characteristic p of any
degree. This uses the existing local extension theorem, not an assumed
classification of integral models.

`ConstantGroupModel` constructs the dual group algebra over a general base.
Its coordinates are the function algebra on the prescribed finite group.
`ConstantGroupPoints` proves that evaluation gives every geometric point and
that its Galois action is trivial. No group order is inverted.
`LocalConstantIdentification` combines this explicit model with rigidity to
identify the original p-killed model when its generic action is trivial.
Integral étaleness is a conclusion.

`OrdinaryLocalConstantQuotient` applies the result to the actual contracted
ordinary quotient. For beta = 1 its integral coordinates are the function
algebra on the given finite coefficient field, with no change of the middle
model. The prescribed point comparison also identifies W48's integral point
above one with evaluation at one. Nontrivial unramified beta still requires
descent or a twist: this
constant identification over the original base is not asserted in that case.

`LocalIntegralScalars` constructs integral coefficient multiplication on the
original model and derives all scalar laws by generic faithfulness.
`OrdinaryLocalScalars` proves that the actual kernel inclusion and quotient
arrows commute with those constructed scalar actions.

Still required: identify the integral kernel as multiplicative, construct its
compatible group-like integral basis, and connect that basis to the torsor's
integral root equation. The newly available local uniqueness theorem reduces
this to an explicit generic comparison with the intended diagonalizable model;
it does not itself supply that comparison. A concrete next route is to extend the rational-only
`FiniteFlatObject.cartierDualPointEquiv` from `IntegralCartierPoints` to `FF R K`,
using the existing general-field `geometricCharactersMulEquiv`. Then prove
that the actual cyclotomic kernel has trivial Cartier-dual action, apply the
new local constant classification to that dual, and use integral biduality.
These general-field comparison and action lemmas are not constructed here.
Discharging the ramification bound for a specified unramified base also remains
an application obligation.

## R1c: actual fibre differences and prime-field root classes

`OrdinaryRootClass` constructs the root-valued coefficient map for prime-field
ordinary filtrations whose ratio character is the specified cyclotomic
character. Its inverse recovers the normalized vector difference. Each section
computes the transported original continuous class, and any simultaneous
continuous twist leaves the root cocycle unchanged.

`OrdinaryIntegralRootDifference` identifies the actual augmentation quotient
with the schematic kernel through the previously proved equality of ideals.
It transports the actual two fibre points' Hopf difference to that kernel and
proves that its root coordinate is precisely the constructed ordinary root
cocycle. No equality of point maps, cocycles or classes is supplied as a premise.
This gives a geometric fibre comparison, not an integral multiplicative
presentation or a proof that its Kummer parameter is a unit.

Still required: the integral multiplicative basis and unit parameter,
compatibility of integral models with the unramified twist, and root-valued
coefficient descent for arbitrary finite residual coefficient fields.

## Later gates retained from W48

Work remains at the first integral-kernel gate; the later gates are not closed
by this delivery. S0a2/S0a3 still need comparison of the finite-DVR uniformizer
character with the specified absolute tame character, the needed surjectivity,
and niveau-two/non-peu and symmetric-power composition-factor results.

L20/D1a still need determinant, flatness at p, other arithmetic local conditions,
simultaneous effectivity and characteristic-zero solutions for the actual HR
universal quotient. The fixed-frame quotient-at-two construction is unchanged.

Lp0 still needs B_cris, Frobenius and crystalline comparison using the existing
family period objects, integral Barsotti–Tate classification including p = 2,
and recovery of the prescribed lattice and levels. No new period object is
introduced here. The global Selmer, modularity, auxiliary-field, finiteness,
coefficient-order and residual-conjugacy gates also remain.

The lifting admission is unchanged. The final endpoint axiom receipt, rather
than these intermediate lemmas, determines whether `sorryAx` remains.
