# Mazur input used by the FLT endpoint

Scope checkpoint: 2026-10-19, GOAL-MAZUR_D_W435. This supersedes the requirement
in `MAZUR_PLAN.md` to prove the universally quantified rational torsion target.
The previous local-arithmetic work is preserved in PREV_DW434_HANDOFF.md;
it is not the next task list. G1 owns moduli and G2 owns Picard/Jacobian work.

## What the checked source already does

The starting revision is `8104e8162`. Contrary to the premise of the new brief,
small exponents are already closed and the endpoint already uses Mazur only
at prime exponents at least seventeen:

- `FltRegular/SmallNumbers/Five/FLT5.lean:13` proves regularity of 5 using
  the cyclotomic class number one theorem, then FLT at line 20.
- `FltRegular/SmallNumbers/Seven/FLT7.lean:15`,
  `Eleven/FLT11.lean:15`, and `Thirteen/FLT13.lean:15` do the same for 7, 11,
  and 13; their FLT theorems are at line 22.
- All four use `flt_regular`, `FltRegular/FltRegular.lean:14`.
- `FltRegular/SmallNumbers/SmallNumbers.lean:15` handles every exponent 3–16,
  using divisibility for composites. `FLT/Basic/Lemmas.lean:60` reduces the
  remaining problem to primes at least 17.
- `FLT/Proof.lean:45` defines B2 with the threshold 17; B3 and B4 retain that
  threshold. `B2_implies_B1` at line 81 supplies the existing small cases.
- `FermatsLastTheorem.lean:23` was the three-input endpoint. Its path ran
  through `Assembly/ThreeInputFinal.lean:24`, `PrimePowerFinal.lean:31`,
  `Assembly/Proof.lean:45`, and `Assembly/Mazur.lean:41`.
- `Assembly/Mazur.lean:25` already restricts `MazurTorsionExclusion` to p≥17.
  `Assembly/ExistingInputs.lean:25` supplies it from `mazur_W`.

Read-only reproduction: inspect those files and run the individual `#print axioms`
checks listed in `Scratch/MazurDW435/Baseline.lean`. Checked at 03:03 UTC:
the four small-prime theorems, `FLT_small`, the reducible-Frey bridge,
`mazur_of_torsionExclusion`, `B4_of_inputs`, and the conditional three-input
assembly all use only `propext`, `Classical.choice`, and `Quot.sound`.
The combined audit used 6.40 GiB RSS; subsequent module probes and audits are
split to respect the requested memory budget. This is not an axiom-removal claim.

## The precise narrow input

For an actual `P : FreyPackage` with `17 ≤ P.p`, require

```lean
have _instPrime : Fact P.p.Prime := ⟨P.pp⟩
GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos)
```

`FLT.Assembly.FreyIrreducibility` quantifies exactly this proposition. The
package already supplies primality, coprimality, normalization, and the Fermat
counterexample equation. There is no claim about all rational elliptic curves,
all semistable curves, all rational torsion, or the full Mazur classification.
This is the exact interface sufficient for the irreducibility/reducibility
contradiction; it is not claimed to be a logically unique weakest proposition.

The sufficient geometric exclusion is more specific than the old interface:
no rational point of order p on the Frey curve or the particular quotient curve
produced from a trivial quotient of its mod-p representation. Both curves have
full rational two-torsion, hence such a point gives an injection of
`(ZMod 2 × ZMod 2) × ZMod p`, equivalently `ZMod 2 × ZMod (2*p)` for odd p.
A lone point of order 2p does not supply the independent two-torsion generator.

A stale comment at `FLT/MazurW.lean:98` calls the equivalence between
`ZMod 2 × ZMod 10` and `(ZMod 2 × ZMod 2) × ZMod 5` erroneous. That equivalence
is in fact correct; the new Chinese remainder theorem proves it. The actual
sanity fixture constructs only cyclic order ten, which is compatible with
Mazur. Its comment must not be read as supplying full two-torsion. The admitted
`mazur_W_ge11` at line 50 is not used by the active endpoint.

The bridge is **`FLT/FreyCurve/Mazur.lean:35`**, not `FLT/MazurW.lean`:
`mazurW_counterexample_of_reducible` uses the unramified character alternative
(lines 48–65). A fixed line gives rational p-torsion on the Frey curve
(lines 68–71). A trivial quotient gives a quotient elliptic curve and p-torsion
(lines 73–76); full two-torsion survives its p-killed kernel (lines 77–79).
`SerrePlan.join_coprime_torsion` joins the two subgroups.
Its public existential result forgets which curve and which quotient produced
the witness. Thus the old interface excludes the configuration on *every*
elliptic curve; that universal statement is sufficient but stronger than needed.

`FLT/Assumptions/Mazur.lean:103` supplies finiteness and the torsion bound 16.
`FLT/MazurW.lean:23` uses that bound to contradict the injected group's order 4p.
It does not need the classification of the fifteen possible groups.
The bound 16 alone already excludes points of order p≥17. For p=5,7,11,13,
that bound alone does not exclude a p-point; the independent two-torsion would
be needed if those exponents had not already been discharged by regularity.

## Active assembly and axiom boundary

`SmallRegularPrimes` gives a direct split into 5, 7, 11, 13, and p≥17,
reusing the proved regular-prime results rather than duplicating class-number
computations. `NarrowFreyFinal` combines this split with `FreyIrreducibility`
and B4. The existing endpoint is rewired only at its final theorem application;
the lifting, family, and three-adic sorting producers retain their existing role.

The instantiated theorem `freyIrreducibility_of_torsionExclusion
mazurTorsionExclusion` is the narrowed theorem derived from `Mazur_statement`.
The active endpoint uses its refined route through
`freyQuotientTorsionExclusion_of_torsionExclusion` and
`freyIrreducibility_of_quotientTorsionExclusion`, retaining the quotient witness.
These conditional theorems are audited with only standard axioms; their current
supplied proof still depends on Mazur. This keeps the requested standard-only audit for new declarations
without pretending that a theorem proved using Mazur has no Mazur dependency.
Legacy alternate assembly theorems remain available, but the active positive-
natural endpoint goes through the narrowed input. Removing the axiom requires
replacing that one supplied proof, not redefining the narrowed proposition.

## Constructive refinements after the scope audit

`FreyCurve/TorsionQuotientWitness` strengthens the old reducibility witness:
it retains the original rational-point map with p-killed kernel, and the
embedded cyclic p-subgroup of its target. The fixed-line branch returns the
identity map. The quotient branch returns the map actually constructed by
`quotient_curve_of_trivial_quotient`; no new witness is postulated.

`Assembly/FreyQuotientExclusion` uses that retained data to give an intermediate
sufficient input, strictly restricted in its quantifiers to actual Frey packages
and targets admitting such maps. It proves that input implies Frey irreducibility
and that the old universal torsion exclusion supplies it. The kernel condition
is the interface exposed by the existing construction, not a definition or
certification of an algebraic p-isogeny. Thus this interface still permits more
targets than the intended geometric isogeny formulation.

`Mazur/CyclicTorsionPoint` constructs the cyclic subgroup embedding from an
exact-order point and proves the converse, making the point formulation precise.
`Mazur/FullTwoPrimeTorsionEquiv` constructs the Chinese remainder equivalence
and transports subgroup embeddings in both directions. These are elementary
bridges, not the missing arithmetic exclusion.

The sole pre-existing Lean edit is the final application in
`FermatsLastTheorem.lean`, following the brief's explicit endpoint-edit allowance.
All other Lean changes are new modules and sorted root imports. None of the
older local-arithmetic, G1, or G2 sources are changed.

## Remaining Eisenstein-ideal work

The scope change does not by itself prove the narrow input. Existing G1/G2
handoffs describe intermediate geometry, not completed modular-curve theorems.
The source ledger in `MAZUR_CONTRACTS.md:98` identifies the following results
from Mazur, *Modular curves and the Eisenstein ideal*, IHÉS 47 (1977):

1. Construct the integral prime-level X0(p), its two disjoint cusps, and the
   moduli map for the actual Frey/quotient pair and its cyclic p-subgroup.
   Prove the needed cusp-specialization statements. G1 owns this construction;
   a universal family on the coarse modular curve must not be assumed.
2. Construct J0(p), algebraic Hecke correspondences, their algebra T, and
   the Eisenstein ideal generated by `1+w` and `1+l-T_l` (l≠p).
   G2 owns the Picard/Jacobian infrastructure.
3. Construct the Eisenstein quotient by the images of the **completion kernel**
   `gamma_I = ⋂ n, I^n`. Quotienting by I itself is the wrong construction.
   Construct its integral abelian model and the Abel–Jacobi projection.
4. Prove its rational-point finiteness (rank zero together with the required
   finite-generation theorem), or precisely the torsion/finiteness statement
   used by the chosen specialization argument. This is arithmetic work;
   the name “Eisenstein quotient” is not a proof of rank zero.
5. Prove that the two cusp images are distinct. The classical order formula
   is numerator((p−1)/12), but this client only needs a nonzero image.
6. Apply integral torsion specialization to the actual Frey configuration,
   propagate the required cusp orientation, and finish the local/global
   contradiction. Mazur III §5, especially Step 3, is not replaced by a local
   discriminant computation. A route through repeated isogenies also needs
   the finite modular-point and endomorphism arguments recorded in MAZUR_PLAN.

No general torsion-classification endpoint, composite-level moduli theory,
or universal local-arithmetic list is required by the narrowed statement.
Construction gaps remain work; this document does not assert that the global
Eisenstein argument is complete or that it follows from the new adapters.
