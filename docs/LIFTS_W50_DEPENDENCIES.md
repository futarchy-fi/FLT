# Lifting gates after W50

The scope of this contribution is the prime-field ordinary integral kernel and
its Kummer unit class. It does not close the lifting theorem. Re-run the saved
read-only check `python3 Scratch/LiftsW50/check.py` for source hashes, line caps,
individual build/lint/axiom receipts, integration ancestry and endpoint audit.
The untracked `LIFTS_W50_RESULT.md` contains the checked timestamp and commits.

## R1a2/R1b3: actual diagonalizable kernel and integral basis

`DiagonalGroupModel` constructs the integral group algebra on any finite abelian
character group over a base with characteristic-zero generic field. Its points
are the actual geometric points of that algebra. `PrimeDiagonalPoints` proves
that primitive-root coordinates exhaust the points for the cyclic degree group
`ZMod p`, preserve addition, and intertwine the specified cyclotomic character.
The surjectivity proof constructs a coordinate from each character's value on
one; no cardinality or point-comparison hypothesis is supplied by the caller.

`OrdinaryLocalDiagonalKernel` extends this prescribed generic comparison to an
integral Hopf isomorphism on the **actual schematic ordinary kernel**, using
W49's local uniqueness theorem. Its hypotheses are:

- the original ordinary filtration over `ZMod p`;
- a chosen primitive p-th root and equality of the kernel character with its
  prime cyclotomic character;
- adic completeness, residue characteristic p, and `order(p) < p - 1` for the
  number-field completion's valuation ring.

The comparison evaluates each integral group-algebra generator in precisely the
specified primitive-root coordinates. `GroupLikeBasisTransport` transports the
basis, group law, comultiplication and counit through an integral bialgebra
isomorphism. `QuotientGroupBasisTransport` proves the diagonal compatibility
needed by the torsor even when its augmentation quotient has not been equipped
with a separate coalgebra instance. `OrdinaryLocalKernelBasis` applies both
constructions to the original kernel and the original augmentation quotient.
The quotient compatibility follows from the actual inclusion's coalgebra law
and the proved equality of the two kernel ideals.

## R1c: original fibre, integral parameter and continuous class

For a trivial quotient character, `OrdinaryLocalUnitParameter` uses the actual
integral point above one and W48's strong-grading theorem. The constructed basis
supplies all that theorem's basis prerequisites. The result is a homogeneous
unit on the original fibre whose p-th power is a unique integral base unit.
Evaluation at every original vector above one satisfies that same root equation.

`OrdinaryLocalRootRatio` evaluates the canonical torsor difference on the
transported basis. Its value is both the ratio of the constructed roots and the
primitive-root coordinate of the original ordinary cocycle.
`OrdinaryIntegralFiberGalois` proves that translating the vector postcomposes its
actual fibre point with the field automorphism.

`OrdinaryLocalKummerClass` combines these equalities to identify the original
continuous root-valued class with the constructed integral parameter. Its final
`ordinaryLocalExtensionClass_unit` proves membership of the transported original
extension class in the independently defined valuation-unit Kummer subgroup.
Root existence in the algebraic closure is proved by the existing API; the final
membership theorem requires no root-existence or class-equality premise.

## Remaining dependencies, in order

1. **R1a2/R1b3/R1c beyond this case:** arbitrary finite residual coefficient fields
   still require coefficient descent or a full character-dual comparison.
   A nontrivial unramified quotient character still requires integral twist/base
   change compatibility and descent. W49's generic twist identity alone does not
   supply this integral comparison. Instantiate the explicit ramification bound
   on the intended unramified base. The small-ramification hypothesis here does
   not address the p = 2 classification. No general integral classification is
   claimed by the prime-field construction.
2. **S0a2/S0a3:** identify the finite-DVR uniformizer character with the specified
   absolute tame character and derive its required surjectivity. Niveau-two,
   non-peu and symmetric-power composition-factor theorems are not supplied here.
3. **L20/D1a:** determinant, flatness at p, other arithmetic local conditions,
   simultaneous effectivity and characteristic-zero solutions on the actual HR
   quotient. W48's fixed-frame quotient at two is unchanged.
4. **Lp0:** B_cris/Frobenius and crystalline comparison on the existing family
   period objects; integral Barsotti–Tate classification including p = 2; recovery
   of the prescribed lattice and levels.
5. Global Selmer, modularity, auxiliary-field, finiteness, coefficient-order and
   residual-conjugacy dependencies remain as recorded in the earlier handoffs.

No existing Lean proof is replaced. The lifting admission and the final endpoint
must be assessed by their axiom audits; these intermediate results do not remove
`sorryAx` from them.
