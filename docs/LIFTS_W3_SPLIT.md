# Lifting wave 3: preserve the prime residual coefficient field

Checked 2026-09-30 UTC at `dfc3f467`: GL1–GL4 are committed.
Evidence: `git log -6 --oneline`; the API searches below are rerunnable.
This subdivides audit L1 (residual coefficient adapters), the next gate after
GL4 in `LIFTS_GOAL_LEDGER.md`. GL2 and
`IsHardlyRamified.isAbsolutelyIrreducible` already supply residual oddness
and absolute irreducibility; do not prove those again.

The source is Khare–Wintenberger, *Serre's modularity conjecture II*,
Corollary 4.7 and §10.3.1 (the characteristic-zero quotient of the deformation
ring), together with §2.1's fixed-residue deformation setup; manuscript:
https://www.math.ucla.edu/~shekhar/papers/proofs.pdf.
Checked directly in `Scratch/kw-proofs.txt`: §2.1 at lines 215–223 fixes
the residue field; Corollary 4.7 at 2584–2598 passes through R/I.
These are algebraic sublemmas of the coefficient/residual-identification row
of the source ledger, not new arithmetic existence results. In particular,
passing to a finite extension's integer ring may enlarge its residue field.
Instead, retain a prime quotient of the original local deformation algebra.

## Common contract and scope

Use namespace `GaloisRepresentation.IsHardlyRamified`. All proposed files
below are in `FLT/GaloisRepresentation/HardlyRamified/`.
For W3.1–W3.2 the exact shared context is:

```lean
variable (p : ℕ) [Fact p.Prime] (D : Type*)
  [CommRing D] [IsLocalRing D] [Algebra ℤ_[p] D]
  [IsLocalHom (algebraMap ℤ_[p] D)] [IsResidueAlgebra ℤ_[p] D]
```

`IsResidueAlgebra` means the coefficient map onto the residue field is
surjective. It is already part of the deformation coefficient category;
this algebraic input is explicit. No record may assume a characteristic-zero
point, nonnilpotence of p, local geometry, or a hardly ramified lift.
All three leaves are READY in the dependency order below, with each cap
including imports and comments. No new declaration may depend on `sorryAx`.

## W3.1 — `PrimeResidualAlgebra.lean`, cap 180, READY

Dependencies: GL1 and `Deformations.IsResidueAlgebra`.
Construct the residue-field equivalence by composing
`(IsResidueAlgebra.algEquiv ℤ_[p] D).symm` with `PadicInt.residueField`.
Compose with `IsLocalRing.residue D` to define `primeReduction`.
Exact statement sketches in the common context:

```lean
noncomputable def primeResidueEquiv : IsLocalRing.ResidueField D ≃+* ZMod p
noncomputable def primeReduction : D →+* ZMod p
 theorem primeReduction_surjective : Function.Surjective (primeReduction p D)
 theorem primeReduction_ker :
    RingHom.ker (primeReduction p D) = IsLocalRing.maximalIdeal D
 theorem primeReduction_comp_algebraMap :
    (primeReduction p D).comp (algebraMap ℤ_[p] D) = PadicInt.toZMod
```

Surjectivity is composition of the residue surjection and equivalence;
use `IsLocalRing.ker_eq_maximalIdeal` for the kernel and GL1 for the
coefficient identity. Consumer: W3.2 and the residual algebra in W3.3.
Source: the fixed-residue coefficient setup preceding II Corollary 4.7.

## W3.2 — `PrimeResidualNaturality.lean`, cap 220, READY after W3.1

Exact sketches (add a second ring `E` with the same common instances):

```lean
 theorem primeReduction_unique (f : D →+* ZMod p) : f = primeReduction p D
 theorem primeReduction_natural (f : D →+* E) :
    (primeReduction p E).comp f = primeReduction p D
```

For uniqueness, `ZMod.ringHom_surjective` makes the kernel of f the maximal
ideal. Subtract a coefficient lift using
`IsResidueAlgebra.exists_sub_mem_maximalIdeal`; GL1 identifies both maps on
that lift. Naturality then follows even without a continuity or algebra-map
hypothesis on f. Consumer: the quotient residual witness in W3.3.
Source: residue compatibility in II Corollary 4.7's quotient construction;
this proves compatibility rather than assuming a second residual model.

## W3.3 — `LiftDomainResidue.lean`, cap 280, READY after W3.2 and GL4

Specialize D to `Type`, add `[Module.Finite ℤ_[p] D]`, take `(P : Ideal D)`
with `[P.IsPrime]` and `(hp : (p : D) ∉ P)`.
Use the quotient instances from `IsResidueAlgebra`; explicitly compose the
local maps D → D/P and ℤ_[p] → D to supply coefficient locality. Exact sketches:

```lean
 theorem primeReduction_quotient_comp :
    (primeReduction p (D ⧸ P)).comp (Ideal.Quotient.mk P) = primeReduction p D
 theorem exists_quotient_residual_algebra [Algebra ℤ_[p] (ZMod p)] :
    ∃ (_ : Algebra (D ⧸ P) (ZMod p)),
      IsScalarTower ℤ_[p] (D ⧸ P) (ZMod p) ∧
      IsLocalHom (algebraMap (D ⧸ P) (ZMod p)) ∧
      Module.Free ℤ_[p] (D ⧸ P)
```

Give the quotient its inherited local and same-residue instances, use W3.1's
map as the algebra, W3.2 for the original residue identification, and GL1
for the scalar tower. GL4 proves freeness; finiteness and domain status are
existing quotient instances. This does not assume D itself is free.
Source: II Corollary 4.7's finite characteristic-zero coefficient quotient.
It remains conditional on p avoiding P; arithmetic must supply that premise.

## API evidence and checks

Rerun these from the repository root (`M=.lake/packages/mathlib/Mathlib`):

```sh
rg -n 'algEquiv|exists_sub_mem_maximalIdeal|isSurjective' FLT/Deformations/IsResidueAlgebra.lean
rg -n 'primeResidueMap_unique|quotient_free_of_prime_avoiding_p' FLT/GaloisRepresentation/HardlyRamified
rg -n 'residueField|toZMod_eq_residueField_comp_residue' "$M/NumberTheory/Padics/RingHoms.lean"
rg -n 'ker_eq_maximalIdeal' "$M/RingTheory/LocalRing/MaximalIdeal/Basic.lean"
rg -n 'ringHom_surjective' "$M/Data/ZMod/Basic.lean"
rg -n 'of_algebraMap_eq' "$M/Algebra/Algebra/Tower.lean"
```

Anchors checked: `IsResidueAlgebra.lean:53,60,86`,
`PrimeResidueMap.lean:18`, `LiftDomainFree.lean:18`,
Mathlib `Padics/RingHoms.lean:349,442`,
`LocalRing/MaximalIdeal/Basic.lean:116`, `ZMod/Basic.lean:1135`.
For each leaf, build in foreground with `LEAN_NUM_THREADS=2 lake build MODULE`,
then `lake exe runLinter MODULE` for that module alone; print axioms of every
new declaration from a scratch Lean file. Commit each accepted leaf locally.
Register modules in `FLT.lean`; check its public imports with `LC_ALL=C sort -c`.

## Boundary after this wave

These leaves fix coefficient reduction and its behavior under GL4's quotient.
They do not supply a residual representation over a chosen matrix frame,
the finite-flat/weight-two dictionary, cyclotomic-restriction irreducibility,
representability of exact local type at 2, arithmetic dimension, or finiteness.
Those remain the ledger's source-matching gates before audit L2 can dispatch.
In particular, `narrowSLiftFunctor` has a different local contract and admitted
representability; neither is a substitute for the required local functor.
The next design dispatch is the finite-flat/weight-two dictionary from
II Proposition 3.6 and §3.2.2, retaining every open coefficient quotient.
