# Lifting gates after W54

The scope remains removal of the lifting admission. The new coefficient-ring
construction does not prove arithmetic nonvanishing or complete that objective.
Validation receipts and exact source hashes are in `Scratch/LiftsW54/`.

## D1a: coefficients and the remaining arithmetic assertion

Use the actual Witt ring W(k) of the specified finite characteristic-p field.
The constructed p-adic scalar embedding is injective. W(k) is a complete
Noetherian DVR, with uniformizer p and residue field canonically identified
with k. The residue equivalence respects the original p-adic algebra structure:
all p-adic ring homomorphisms to a characteristic-p field coincide.

Transport the original residual representation along the inverse residue
isomorphism. Surjective coefficient change preserves its hardly-ramified
conditions, so W53's actual arithmetic and finite-flat quotient applies to it.
The resulting lift retains its original residual representation under this
specified coefficient identification, its cyclotomic determinant, its inertia
conditions away from 2p, its specified quotient row at two, and its finite-flat
open reductions at p.

For any W(k)-algebra A, the following are equivalent:

- W(k) embeds into A by the structure map;
- p is not nilpotent in A;
- A has characteristic zero.

Consequently the actual flat quotient has characteristic zero exactly when
all powers of p avoid its defining ideal. This is also equivalent to existence
of a continuous proartinian characteristic-zero specialization. These are
criteria, not proofs that the criteria hold. Under a separate Noetherian
hypothesis on the effective quotient, a prime avoiding p is closed and gives
a continuous characteristic-zero domain specialization. No Noetherian
hypothesis on the deformation quotient has been discharged here. A domain
specialization is not yet a finite extension of Q_p or the required coefficient
order.

The next D1a proof must show nonvanishing on this actual mixed-characteristic
arithmetic quotient; it cannot replace that proof by a field-valued point or
an injective structure map supplied as a hypothesis.

## S0a2 and S0a3

The existing `finiteIdealInertiaRestriction_surjective` already proves
surjectivity from absolute inertia to the actual finite ideal inertia model.
The new absolute tame-character result identifies the repository's specified
`tameCharacter` with the chosen reduced root character and proves surjectivity
onto the full residue unit group. These are different surjectivity statements.

`FiniteUniformizerRootCharacter` constructs the actual integral-closure inclusion
from a finite Galois field and proves it is local. If a finite uniformizer is
an n-th root of a nonzero base element, its integral ratio and reduced character
are the absolute root ratio and character. For a (q-1)-st root of a base
uniformizer this identifies it with the specified `tameCharacter`, using the
constructed residue maps. The root and uniformizer hypotheses are explicit;
no character-evaluation premise is substituted for this proof.

Still required: produce the appropriate finite root-uniformizer model for the
intended representation and handle the ramification exponent in general.
Surjectivity of the finite uniformizer character onto every residue unit is
not automatic: an unramified extension has trivial inertia. Do not silently
reuse a theorem requiring that extra surjectivity hypothesis.

Niveau-two, non-peu and symmetric-power composition-factor classification
remain. No Serre-weight evaluation or arbitrary-p Raynaud classification API
is assumed to exist.

## R1

`OrdinaryFiltration.twist` constructs the actual scalar twist and the existing
`extensionClass_twist` identifies its class. `existsUnique_unramified_descent`
constructs continuous descent of inertia-trivial characters through the actual
unramified quotient. Neither theorem constructs descent of the finite-flat
integral model of the twisted representation.

`UnramifiedCharacterSplitting` proves the constructed finite character is
faithful, its Galois group has prime-to-p order, and its integral inertia is
trivial when the original character is unramified. Restriction to the actual
open splitting subgroup kills the character. This supplies the finite
field-level splitting step, not effective descent of the integral model.

Still required: the nontrivial unramified quotient twist at the integral-model
level, finite unramified base extension, effective descent with its cocycle,
and the small-ramification bound on the intended base. A character-factorization
or generic cocycle identity does not close this gate. The existing unit-model
bound does not cover p = 2.

## Lp0: split before constructing B_cris

These are construction tasks, not hypotheses in a lifting record.

| Leaf | Actual inputs | Required output |
|---|---|---|
| C0a.1 | `Ainf p`, its Witt ring, `complexAinfGalois`, `complexThetaGenerator` | Witt Frobenius on this ring; equivariance and its effect on the theta generator |
| C0a.2 | The same theta kernel and A_inf[1/p] | Integral divided-power envelope, p-adic completion A_cris, and a proved Frobenius extension |
| C0a.3 | A_cris, `complexCyclotomicFieldPeriod`, `ComplexBDeRham p` | Invert p and the crystalline Tate period; construct a Galois-equivariant map to that exact de Rham field |
| C0b | B_cris with those actions and maps | Tensor invariants and the canonical comparison maps; fixed scalars and dimension bounds |
| C0c | The family's existing de Rham eigenperiod/filtration results | Crystalline trivial and cyclotomic normalization, with Frobenius and weight -1 for the covariant Tate twist |
| C0d | Constructed comparisons | Coefficient, tensor, dual and restriction naturality |
| C1–C4 | These rational comparisons and the actual finite-flat quotient | Integral Barsotti–Tate recovery of the specified lattice, its levels and both directions of comparison, including p = 2 |

C0a.1 is proved in `ComplexAinfFrobenius`: the actual Witt Frobenius commutes
with the existing Galois action and fixes the existing p-adic scalar embedding.
The other C0a leaves and all comparison leaves remain open.

Frobenius on A_inf must not be assumed to descend through theta: for the
actual generator ξ = [p-flat] - p, theta(phi(ξ)) = p^p - p is nonzero.
The divided-power construction and its topology are essential additional work.
