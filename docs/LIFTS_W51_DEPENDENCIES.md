# Lifting gates after W51

This contribution extends the ordinary integral kernel comparison and unit-class
construction from `ZMod p` to arbitrary finite residual coefficient fields.
Validation receipts and their checked timestamp are in the untracked
`LIFTS_W51_RESULT.md`. Re-run `python3 Scratch/LiftsW51/check.py` to check source
hashes, line caps, serial build/lint/axiom receipts, integration and endpoint audit.

## Finite coefficients

`PrimeDualCharacters` identifies all characters of a prime-field module with
its linear dual using actual roots of unity. `FiniteDiagonalPoints` applies
biduality to construct every geometric point of the integral group algebra on
`Module.Dual (ZMod p) k`. Point evaluation on a group-like generator indexed by
`a` is the chosen primitive root raised to `a x`. The comparison is additive,
bijective and equivariant for the scalar-extended prime cyclotomic character.
Neither a trace-pairing premise nor a point-counting premise is needed.

`OrdinaryFiniteDiagonalKernel` extends this prescribed comparison to an integral
Hopf isomorphism on the **original schematic kernel** using local uniqueness.
`OrdinaryFiniteFiberDifference` identifies the original augmentation quotient
with that kernel and computes its fibre difference for any coefficient field.
`OrdinaryFiniteKernelBasis` transports the group-like basis and its diagonal
compatibility to the actual augmentation quotient.

For each prime-linear functional `a : k →ₗ[ZMod p] ZMod p`,
`OrdinaryFiniteUnitParameter` constructs a homogeneous unit of degree `a` on
the original integral fibre above one. Since `p • a = 0`, its p-th power is a
unique integral base unit. `OrdinaryFiniteRootRatio` identifies the evaluated
root ratio with `a` applied to the original ordinary cocycle at one.

`FiniteRootProjection` and `OrdinaryFiniteRootClass` construct the projections
of the original continuous extension class, independently of the integral
construction. `OrdinaryFiniteKummerClass` proves that every such projected
class has the constructed integral unit parameter. `FiniteUnitReconstruction`
expresses the original class as a finite sum of scalar extensions of its root
projections. `OrdinaryFiniteUnitClass.ordinaryFiniteExtensionClass_unit` thus
places the original class in the existing, basis-independent
`extendedUnitSubspace`; its membership is not a new definition of flatness.

The arithmetic hypotheses remain a number-field completion, adic completeness,
residue characteristic p, `order(p) < p - 1`, a chosen primitive p-th root,
a cyclotomic kernel character, and a **trivial quotient character**. The
coefficient field is finite with an algebra structure over `ZMod p`. No
parameter-existence, class-equality or integral-classification premise is added.

## Remaining dependencies, in order

1. **R1a2/R1b3/R1c:** integral compatibility with a nontrivial unramified quotient
   twist, base extension and descent; instantiate the small-ramification bound
   on the intended unramified base. The existing generic twist identities do not
   prove this integral descent. The bound does not cover the p = 2 case.
2. **S0a2/S0a3:** compare the finite-DVR uniformizer character with the specified
   absolute tame character, prove the required surjectivity, then niveau-two,
   non-peu and symmetric-power composition-factor results. No unavailable
   Serre-weight or arbitrary-p Raynaud classification API is presumed.
3. **L20/D1a:** determinant, flatness at p, other arithmetic local conditions,
   simultaneous effectivity and characteristic-zero solutions on the actual
   hardly-ramified quotient.
4. **Lp0:** B_cris, Frobenius and crystalline comparison on the existing family
   period objects; integral Barsotti–Tate classification including p = 2;
   recovery of the prescribed lattice and levels.
5. The previously recorded global Selmer, modularity, auxiliary-field,
   finiteness, coefficient-order and residual-conjugacy gates remain.

No existing Lean proof is replaced. The lifting admission is still present in
`FLT/GaloisRepresentation/HardlyRamified/Lift.lean`; the final endpoint must be
assessed by its axiom audit, not by completion of these intermediate lemmas.
