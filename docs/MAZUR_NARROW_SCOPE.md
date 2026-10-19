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
supplied proof still depends on Mazur. This keeps the requested standard-only
audit for new declarations
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

## Rational scheme morphism checkpoint (W451, 2026-10-19)

`FreyCurve/VeluTargetSchemeMorphism` proves that every nonidentity target in
the existing `FreyPackage.IsVeluTarget` witness receives an actual rational
scheme morphism from the original Frey cubic. It preserves the base and zero,
has finite locally free degree p, and has the original rational closed kernel
as its full Cartesian identity fiber. The theorem retains the original
surjective invariant torsion quotient and the exact target equation.

The construction in `Serre/VeluCoefficientOverlapCover` transfers the original
Galois evaluations to graphs covering every point of the actual source overlap.
Reducedness of that overlap makes these graphs detect morphisms to separated
targets. `VeluCoefficientInvariantDescent` then proves full kernel-pair
compatibility and constructs the descended map by effective-epimorphism descent.
`VeluPrimeRationalDegree` and `VeluPrimeRationalKernel` prove its degree and kernel;
the geometric map is recovered in the original Cartesian coefficient square.

Read-only checks for this checkpoint: build
`FLT.FreyCurve.VeluTargetSchemeMorphism` with `LEAN_NUM_THREADS=2 lake build`,
and print axioms of `FreyPackage.IsVeluTarget.exists_prime_scheme_morphism`
after importing that module. Its allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
At the W451 checkpoint, rational group compatibility and the local-model
comparison were still open. W452 below closes the group and point compatibility
and constructs the local generic maps. Integral extension, the modular point,
cusp specialization, and `FreyVeluTorsionExclusion` remain open.
The active endpoint still uses `Mazur_statement`; these constructions do not
replace the arithmetic exclusion or the G1/G2 constructions.


## Rational group quotient and local generic models (W452, 2026-10-19)

`Serre/VeluDescendedGroupMorphism` proves multiplication compatibility for the
actual descended morphism on the existing source and target group schemes.
`Serre/VeluPrimeRationalPointComparison` identifies its geometric values with
`torsionQuotientPointHom` and its rational values with every original quotient
map retaining that base-change square. The original quotient-line embedding
is also identified with the image of geometric torsion.

`FreyCurve/VeluTargetGroupMorphism` assembles a rational group homomorphism for
each retained nonidentity target. Its carrier is the original degree-p scheme
map, with the original rational closed kernel as its full Cartesian identity
fiber. The theorem retains the exact target equation and both original
point-descent squares, together with an injective rational p-torsion map.

`Mazur/WeierstrassGroupHomCoefficient` and
`Mazur/WeierstrassGroupHomVariableChange` construct actual Cartesian transports
of group morphisms and preserve their finite locally free degree.
`Serre/VeluLocalGenericMorphism` applies them to the original rational quotient
on any specified local source and target equations with their actual generic
variable changes. Both Cartesian squares and the composite rational comparison
are proved, so the chosen equations do not replace the original quotient.

`Mazur/RationalPadicMinimalGroupMorphism` constructs minimal equations for both
ends, with a generic group morphism of the original degree.
`FreyCurve/VeluTargetLocalGenericMorphism` applies this construction at every
rational prime, including p. For p >= 17, the same original rational p-subgroup
transports injectively to the target minimal equation, with exact order p and
proved good or multiplicative reduction. Its rational group map still agrees
with the original point quotient.

These maps are on the generic fibers of integral minimal equations. Extension
to the appropriate smooth or generalized integral models, the original kernel
closure and its modular interpretation still require construction. Regularity
on an entire singular Weierstrass model is not asserted. The explicit point
comparison through the local variable changes, an actual prime-level modular
point, cusp orientation and specialization remain work. Negative j valuation
alone does not select a cusp. G1's moduli and G2's Picard/Jacobian lanes remain
separate from this construction.

Read-only checks: build `FLT.FreyCurve.VeluTargetLocalGenericMorphism` with
`LEAN_NUM_THREADS=2 lake build` and print axioms of
`FreyPackage.IsVeluTarget.exists_prime_group_morphism` and
`FreyPackage.IsVeluTarget.exists_padic_minimal_generic_quotient` after importing
that module. Each theorem must use only `propext`, `Classical.choice` and
`Quot.sound`. The local receipt checker is `python3 Scratch/MazurDW452/check.py`;
its checked-at timestamp, source hashes and logs are retained in the W452 handoff.

## Specified local points, original kernels and schematic closure (W453, 2026-10-19)

`Serre/VeluAffinePointVariableChange` identifies the actual cubic isomorphism
with the original affine point equivalence, including infinity and the inverse
change. `VeluLocalPointTransport` retains the original field embedding followed
by the specified inverse change. `VeluLocalPointMorphism` uses the Cartesian
local projection to identify point values from the original morphism square.
`VeluLocalGenericPointComparison` applies this to the retained rational quotient.

`Mazur/RationalPadicProjectiveSchemeTransport` identifies the generic scheme
points of the original `rationalPadicProjectiveHom`.
`Serre/VeluPadicGenericPointComparison` proves the theorem
`WeierstrassCurve.Velu.primeLocalGenericGroupHom_padicProjectivePoint`: the actual local quotient
maps these specified source sections to the specified target sections. It works
at every rational prime, including p, with the actual chosen variable changes.

`Mazur/WeierstrassLocalGenericKernel` constructs the pullback of the original
embedded scheme along the actual local projection. Closedness is preserved.
`Serre/VeluLocalGenericKernel` proves that this same original kernel is the
entire Cartesian identity fiber of the actual local quotient and retains
finite locally free degree p over the local field. No abstract replacement
of the rational kernel or target equation is made.

`Mazur/WeierstrassGenericKernelClosure` then constructs the schematic image of
that generic inclusion in the original integral cubic. It is a closed proper
integral subscheme, with the original generic scheme mapping schematically
densely into it. Flatness over a principal domain follows from flatness of the
generic source. `Serre/VeluLocalIntegralKernelClosure` derives this flatness
from the proved prime degree and packages the actual proper flat closure.
This is a construction of the original integral closed scheme, not a claim
that the quotient extends over an entire singular Weierstrass model.

At the W453 checkpoint, generic-fiber recovery and finiteness were still open;
W454 below constructs both. Group operations on suitable smooth/generalized
models, extension of the original quotient, and modular specialization remain open.
`FreyVeluTorsionExclusion` and removal of `Mazur_statement` remain open.
G1's moduli and G2's Picard/Jacobian work remain separate.

Read-only checks: build the two modules `FLT.FreyCurve.Serre.VeluPadicGenericPointComparison`
and `FLT.FreyCurve.Serre.VeluLocalIntegralKernelClosure` individually, and print
axioms of `WeierstrassCurve.Velu.primeLocalGenericGroupHom_padicProjectivePoint`
and `WeierstrassCurve.Velu.exists_primeLocalIntegralKernelClosure`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The local checker `python3 Scratch/MazurDW453/check.py` records checked-at time,
source hashes, build/lint receipts, axiom audits and the merged-main root build.


## Original generic recovery and finite flat degree-p closure (W454, 2026-10-19)

`Mazur/FlatMonoSchematicClosure` proves that a closed subscheme is recovered by
pulling back its schematic closure along a flat monomorphism. The comparison
is both closed and schematically dense. `WeierstrassGenericKernelRecovery`
applies this to the actual coefficient projection and constructs the generic
fiber isomorphism, preserving both original projections.
`Serre/VeluLocalIntegralKernelRecovery` retains the exact original prime kernel.

`Mazur/ProperDenseFiniteSections` bounds each fiber by finitely many section
values. `ProperSplitGenericFiniteness` constructs those sections by properness
and obtains the finite point cover from a finite scheme over an algebraically
closed field, without discarding nilpotents. `ValuationFieldFlatCover` constructs
a dominating, faithfully flat valuation ring inside the specified field.
`ProperValuationGenericFinite` retains the actual generic finite scheme under
scalar change and proves descent of finite fibers. `ProperFlatValuationFinite`
then proves that a proper flat valuation model with finite generic fiber is
finite over its original base, without a splitting assumption there.

`Mazur/SchematicDenseBezoutFlat` and `WeierstrassValuationKernelClosureFlat`
prove flatness of the same schematic closure over arbitrary valuation rings.
`WeierstrassValuationKernelClosureFinite` proves its finiteness over the original
ring. `WeierstrassValuationKernelClosureDegree` recovers the original generic
degree on every integral fiber over a Noetherian valuation base, hence a DVR.

`Serre/VeluLocalIntegralKernelFinite` applies these constructions to the retained
original prime kernel. It proves finite flatness and, over a Noetherian valuation
base, finite locally free degree p. The original inclusion, rational target,
variable changes and full generic-fiber square are retained. No invertibility
of p on the integral base is assumed.

Still open: construct subgroup operations on the required smooth/generalized
integral models, extend the original quotient on those models, and connect the
result to the actual prime-level modular point and specialization. No regular
quotient map on the whole singular cubic is asserted. `FreyVeluTorsionExclusion`
and removal of `Mazur_statement` remain open; G1/G2 retain their existing lanes.

Read-only checks: individually build and lint
`FLT.FreyCurve.Serre.VeluLocalIntegralKernelFinite`, and print axioms of
`WeierstrassCurve.Velu.primeLocalIntegralKernelClosure_finite_flat`,
`WeierstrassCurve.Velu.exists_primeLocalIntegralFiniteFlatKernel`, and
`WeierstrassCurve.Velu.primeLocalIntegralKernelClosure_degree`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
`python3 Scratch/MazurDW454/check.py` reports checked-at time, hashes, individual
probe/build/lint receipts, axiom audits, main ancestry and the root-build result.
