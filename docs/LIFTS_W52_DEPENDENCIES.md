# W52: split the remaining arithmetic quotient obligations

The starting object is `hardlyTwoUniversalObject`, constructed from the actual
HR representation and its chosen surjective quotient at two. Its fixed frame
is part of the condition. The following are separate proof obligations:

| Leaf | Required artifact | Dependency |
|---|---|---|
| D1a-det | Closed determinant ideal and its universal property, specialized to the original HR residual determinant | Existing profinite framed ring and HR frame |
| D1a-away | Closed equations for triviality on every inertia group away from 2p, with residual properness from HR | Actual inertia embeddings |
| D1a-flat | Identify the finite-flat reduction predicate at p with an effective closed condition | Finite-flat model closure and effectivity |
| D1a-all | Simultaneous arithmetic quotient retaining the actual representation and its local quotient | All three preceding leaves |
| D1a-char0 | Produce a characteristic-zero point of that arithmetic quotient | Arithmetic dimension/non-torsion argument, not merely residual properness |
| S0a2 | Compare the finite-DVR uniformizer character with the specified absolute tame character | Absolute/finite inertia comparison and surjectivity |
| S0a3 | Niveau-two/non-peu and symmetric-power composition factors | Actual representation-theoretic classification |
| R1-descent | Unramified quotient twist, integral base extension and descent | W51 finite-coefficient unit class, ramification bound on the intended base |

A nonzero residual point only proves that an ideal is proper. It does not show
that p survives in its quotient, that a characteristic-zero point exists, or
that the universal local representation has finite-flat reductions. No assumed
evaluation, comparison isomorphism, or record field can replace these proofs.

## Implemented equation quotient

`FramedDeterminantIdeal` and `FramedTrivialityIdeal` construct closed ideals
from determinant defects and entries of the action minus the identity.
Their kernel criteria identify continuous solutions with the stated matrix
conditions. `FramedArithmeticIdeal` closes their sum with the existing
specified quotient-row ideal and proves the simultaneous criterion.

`UniversalArithmeticQuotient` applies these ideals to the constructed profinite
universal framed representation. One residual point satisfies all equations,
proving simultaneous properness. The equivalence with constrained continuous
framed lifts is constructed. The map from the previous local quotient is the
actual quotient factor, is proved surjective, and preserves the original
universal parameters.

`HardlyRamifiedArithmeticResidual` identifies the inertia equations with
`GaloisRep.IsUnramifiedAt` at every rational prime away from 2p. It proves the
inertia and determinant residual equations from the original HR hypothesis
and the frame already constructed at two. A subtlety is that the canonical
rational algebra and the adic-completion algebra have propositionally equal
structure maps; uniqueness of rational ring maps supplies the comparison.

`HardlyRamifiedArithmeticQuotient` constructs `hardlyArithmeticObject` from
that same original HR representation, without adding residual matrix equations
as inputs. The coefficient base is a Z_p-algebra whose action on its residue
field agrees with the given residual Z_p-action. The construction remains in
Type 0, as in W48. Its universal lift has the prescribed determinant,
unramifiedness away from 2p, and the fixed quotient at two. Every classified
lift specializes this universal lift on every matrix entry.

`HardlyRamifiedArithmeticAtTwo` proves that every such specialization has upper
character equal to the restricted cyclotomic determinant times the fixed sign
character. It constructs the equivariant surjective coordinate quotient. These
are assertions about the original quotient's specialized representation.

## Remaining mathematical gates

- **D1a-flat:** `flatFunctor` in `FLT.Deformations.LiftFunctor` defines the
  finite-flat reduction predicate and proves preservation by coefficient maps.
  This does not prove closure under the products, subobjects and limits needed
  to identify that predicate with a closed ideal on `hardlyArithmeticObject`.
  An effective ideal and equivalence with the actual finite-flat predicate at p
  are still required. The admitted corepresentability theorems in
  `FLT.Deformations.Representable` are not used by the new constructions.
- **D1a-char0:** even after imposing flatness, prove a characteristic-zero
  solution on that very arithmetic quotient. Residual properness and the
  constructed surjection do not prove p-torsion-freeness, a dimension bound,
  or a characteristic-zero point. A coefficient base and the arithmetic
  non-torsion/dimension argument remain to be supplied constructively.
- **Lp0:** the crystalline comparison and integral Barsotti–Tate effectivity,
  including p = 2, remain separate from these polynomial equations.
- **S0a2/S0a3:** finite-DVR versus specified absolute tame character, requisite
  surjectivity, niveau-two/non-peu and symmetric-power composition factors
  remain unchanged. No nonexistent evaluation/classification API is assumed.
- **R1:** unramified-quotient twist, base extension and integral descent, and
  the ramification bound on the intended unramified base remain unchanged.
- The global Selmer/modularity, auxiliary-field, finiteness, coefficient-order
  and residual-conjugacy gates remain. The lifting endpoint is not discharged.

Validation is executable with `python3 Scratch/LiftsW52/validate.py` (untracked):
foreground two-thread builds, one module per lint invocation, and an axiom audit
of every new named declaration. `LIFTS_W52_RESULT.md` records the checked receipts
and the integration build; it is an untracked handoff, not a theorem claim.
