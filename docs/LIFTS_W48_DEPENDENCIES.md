# Lifting gates after W48

The untracked `Scratch/LiftsW48/validate.py` runs foreground two-thread builds,
individual module lint, and axiom audits of every named declaration. The
untracked `LIFTS_W48_RESULT.md` records saved receipts and the final root check.
These constructions do not establish the lifting endpoint.

## R1a2/R1b3/R1c: construct the integral quotient point and its fibre

`IntegralFixedPoints` proves that a Galois-fixed geometric point of the specified
finite flat model over an integrally closed domain extends uniquely to an
integral point. Integral coordinates are integral over the base; Galois
invariance puts their values in the fraction field; integral closedness puts
them in the base. This does not require the model to be étale.

`OrdinaryIntegralQuotientPoint` applies this to the actual contracted ordinary
quotient. It constructs the integral point above one when beta is trivial and
identifies its tensor fibre with the original vectors projecting to one.
It also proves the converse: an integral point with this geometric value forces
beta to be trivial. An unramified but nontrivial beta therefore cannot simply
be treated as a constant quotient over the original base field.

`OrdinaryIntegralFiberCocycle` constructs both fibre points from a vector above
one and its Galois translate. Restriction to the original middle coordinates
is proved. The actual Hopf difference equals the injected coefficient of the
original Hom cocycle, with neither a point comparison nor a cocycle equality
supplied as a premise. This result is for beta = 1.

The actual integral multiplicative-kernel classification remains missing.
The available order-three extension theorem is restricted to models over
Z_3 with three geometric points; it does not cover arbitrary prime p or
non-prime coefficient fields. In the intended unramified odd-prime setting,
a full integral rigidity/classification argument is needed before W46's
multiplicative basis can be constructed. For general ramified bases, generic
characters alone do not specify an integral model. Still required: the
constant integral quotient identification, the root-valued kernel coefficient
map, equality in ContinuousClass, and compatibility with the unramified twist
and residual coefficient descent. The new integral point does not prove these.

## S0a2/S0a3: actual absolute-to-finite inertia comparison

`FiniteCharacterInertia` constructs the open normal kernel of the given
continuous absolute character, its finite Galois fixed field and descended
character. Restriction recovers the original character. Absolute inertia
surjects onto the actual ideal inertia of the integral closure in this field.
That closure is the finite DVR used in the wild-kernel theorem; its action is
proved faithful through its fraction field. The original absolute character
kills the pulled-back uniformizer-character kernel for finite characteristic-p
coefficients.

`OrdinaryFiniteDVRAction` derives continuity of the subcharacter and quotient
ratio from the actual ordinary representation's orbit maps. It uses that ratio
to construct the finite field and proves the original absolute action equation
on the pulled-back wild kernel. No finite-model comparison is an input.

This finite field depends on the ratio character. Its uniformizer character
has not been identified with the specified absolute niveau-one character,
and surjectivity onto the full specified coefficient-unit group is not
asserted. In particular no claim is made that the absolute niveau-one kernel
is a p-group. The niveau-two/non-peu input and S0a3 symmetric-power
composition-factor comparison remain open; no numerical Serre-weight or
arbitrary-p Raynaud API is assumed.

## L20/D1a: impose the actual HR quotient at two

`SurjectiveQuotientFrame` constructs a kernel basis and a lift of one from an
actual rank-two surjective functional. `RankOneCharacter` reads the unit-valued
character of a scalar representation and proves the quadratic property.

`HardlyRamifiedTwoQuotient` extracts the functional and quotient action directly
from the given `IsHardlyRamified.isTameAtTwo`. It frames the original global
representation, derives the local residual row, and constructs the fixed
integral sign character. That character is proved trivial on the original
inertia group at two. The actual global universal ring's closed quotient then
classifies global framed lifts with this specified local quotient character.
The residual filtration/row obligation at two is discharged, rather than
reintroduced as an input. This construction is currently stated in Type 0.

The specified-frame condition is stronger data than an existential unframed
quotient; closedness of the latter is not claimed. The determinant, flatness
at p, other local conditions, simultaneous effectivity and characteristic-zero
solutions remain required for the full lifting theorem. Properness of this
one quotient does not supply any of those arithmetic conclusions.

## Lp0: exact filtration degree in the existing period field

`ComplexEigenperiodFiltration` uses the family's original B_dR, logarithmic
period and integer filtration. Every chi^n eigenperiod belongs to Fil^n; it
belongs to Fil^(n+1) exactly when it is zero. This gives the exact degree -1
for a nonzero invariant coefficient of the covariant Tate twist, using W47's
unique scalar-multiple classification. There is no replacement period ring.

B_cris, Frobenius, crystalline comparison, general filtered tensor invariants,
coefficient naturality, integral Barsotti–Tate classification (including p=2)
and recovery of the given lattice/finite-flat levels remain open. The exact
rank-one filtration calculation does not discharge the comparison gate C0.
