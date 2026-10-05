# G2 Picard/Jacobian foundation — W1

Checked 2026-10-04 against FLT `55366a692a3cbda66d2dbea4d63e58ef88a42990`
and Mathlib `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
This is the foundation queue for MAZUR_CONTRACTS G2-A1, not a proof of
G2-A1 or of Mazur. W74 in wt-r5a owns G1 ampleness/moduli; none of those
modules is assigned here. Its inspected head was `8fcfa423`.

## Source audit

Reproduce with `rg -n 'Picard|AbelianVariety|relative Picard' FLT/Mazur
.lake/packages/mathlib/Mathlib/AlgebraicGeometry` and inspect the files below.

| Object | Existing implementation | Missing part |
| --- | --- | --- |
| Ring Picard group | Mathlib `RingTheory/PicardGroup`: `CommRing.Pic`, tensor multiplication, dual inverse, scalar extension, local-ring triviality | Scheme Picard group and comparison on affine schemes |
| Relative ring Picard | `CommRing.relPic R A` is the **kernel** of scalar extension | This is not the relative geometric Picard functor, whose presheaf is a **cokernel** of base pullback |
| Line bundles | FLT `DivisorInvertibleSheaf`: `LocallyFreeRankOne`; `ModuleLineBundlePullback`: arbitrary pullback; `CartierTensorRank`: tensor closure | Isomorphism classes and their group/functor structure |
| Dual and tensor | `ModuleSheafDualSheaf`, `DivisorLineBundleSheaf`, `ModuleSheafTensorAssociator`, `ModuleLineBundleTensorPullback` | General rank-one evaluation isomorphism (the existing `DivisorIdealEvaluation` treats Cartier ideals) |
| Divisors | `DivisorLineBundleSum`, `SmoothSectionCartier`, `RelativeCartierBaseChange` | Full divisor class comparison, degree, graph-minus-basepoint universal family |
| Descent | Unit-cocycle gluing and module sheaf pullback are available | fppf descent of line bundles, relative Picard sheafification and representability |
| Abelian varieties | Mathlib `AlgebraicGeometry/Group/Abelian`: proper geometrically integral group schemes over a field are commutative | Picard identity component, Jacobian existence, smoothness/properness, abelian quotients |
| “Jacobian” | Mathlib `EllipticCurve/Jacobian` supplies Weierstrass coordinate formulas | It is not a curve's Jacobian variety |
| Arithmetic | Continuous/group/sheaf cohomology, finite flat group schemes, heights and Northcott | General abelian-variety Mordell–Weil and the actual general-prime finite-flat arithmetic used by Mazur |

`FLT/MazurChapter/AdmissibleGroupSchemes.lean` still contains admissions
(`rg -n 'sorry'`); it is not a source of proved G2-C producers.
The G1-D Néron-model gates remain separate from proper-section extension.
No formal group law or rank-finiteness field may replace their proofs.

## First executable leaves (strict cap: 240 physical lines per new module)

Implement in this order. Each statement concerns actual module sheaves;
there is no structure field supplying Picard representability or G2Finite.
The references for these elementary constructions are the definition of
Picard group as invertible sheaves modulo isomorphism, and the existing
named Lean lemmas in the audit above. No deep existence theorem is invoked.

| Leaf | New module in FLT/Mazur | Exact output | Dependencies | Cap |
| --- | --- | --- | --- | --- |
| P1 | SchemePicardClasses | Quotient of locally free rank-one sheaves by actual module isomorphism; tensor commutative monoid; equality iff isomorphism | Existing tensor/restriction APIs | 240 |
| P2 | LineBundleDualEvaluation | Dual remains locally rank one; canonical evaluation is an isomorphism, proved locally using trivializations and open-cover detection | Existing dual restriction/naturality | 240 |
| P3 | SchemePicardGroup | Dual descends to inversion; Picard commutative group with tensor cancellation | P1, P2 | 240 |
| P4 | SchemePicardPullback | Pullback group homomorphisms, identity/composition laws, contravariant group-valued functor | P3, existing pullback comparisons | 240 |
| P5 | RelativePicardQuotient | Cokernel `Pic(X)/range(f*)`; quotient equality criterion; comparison maps for commuting squares | P4 | 240 |
| P6 | PointedPicardNormalization | Given a section e of f, normalized class L / f*(e*L); prove kernel membership, base-twist invariance, and relative quotient equivalence to ker(e*) | P5 | 240 |

The Picard class type initially lives in the module-sheaf universe. A small
model is a later proved construction, not an unjustified `Small` instance.
P5 is the relative **presheaf value**; neither P5 nor P6 asserts fppf
sheafness. Kernel classes in P6 mean trivializable restriction, not a chosen
rigidification or descent data.

## Remaining construction gates, in dependency order

Each row is a distinct mathematical obligation with a 240-line *per-module*
cap. These are gated targets, not a claim that the proof fits in one file.
Before dispatching a gated row, fix a source proof and split its internal
lemmas further if necessary; no 240-line representability wrapper counts.
The source entry for the final application remains [M] II §6 pp. 88–89;
representability and the Jacobian require independent foundations beyond [M].

| Gate | Required statement | Depends on | Dispatch status |
| --- | --- | --- | --- |
| P7 | Identify affine scheme line bundles with invertible ring modules, compatibly with tensor/pullback | P4, affine module equivalence | Implemented in W2; checks below |
| P8 | Build the relative presheaf on `Over S` using actual fiber-product pullbacks and prove its composition laws | P5 | Implemented in W2; checks below |
| P9 | Construct line-bundle descent along faithfully flat affine maps; prove effectiveness | P7 | Coalgebra module descent implemented; geometric cocycle and invertibility descent remain |
| P10 | Prove fppf descent on schemes and construct relative Picard sheaf with presheaf comparison | P8, P9 | Needs site/base-change subdivision |
| P11 | Rigidified line bundles have trivial relative automorphisms under universally O-connected proper fibers | P6, cohomology/base change | Needs automorphism and H0 comparison |
| P12 | Define degree on line bundles on smooth proper curves, prove tensor additivity and base-change invariance | P7, divisor/degree comparison | Needs divisor-class and degree subdivision |
| P13 | Construct effective-divisor parameter spaces of large degree and their universal Cartier divisor | G1 curve geometry | Needs Hilbert/symmetric-power existence proof |
| P14 | Prove large-degree Abel-map fibers are the appropriate projective bundles using Riemann–Roch | P10, P12, P13 | Needs Riemann–Roch and cohomology comparison |
| P15 | Descend the large-degree parameter space to a representing Picard scheme | P11, P14 | Representability source-design gate; no existence field allowed |
| P16 | Construct the degree-zero component and prove its group law and base-change comparison | P12, P15 | Gated on actual representative |
| P17 | Prove smoothness of degree-zero Picard by lifting line bundles across square-zero thickenings | P16 | Needs obstruction proof |
| P18 | Prove properness and geometric connectedness of degree-zero Picard | P16 | Needs valuative/specialization proof |
| P19 | Construct the universal graph-minus-basepoint line-bundle class over the curve | P8, section Cartier theory | Needs universal diagonal construction |
| P20 | Apply representability to P19, prove basepoint maps to identity and degree zero | P16–P19 | Produces general Abel–Jacobi morphism |
| P21 | Instantiate with actual X0(p) and infinity to obtain J0(p) and G2-A1 | G1-C, P20 | Modular curve/cusp producer still required |

Abelian quotient, norm/pushforward, Néron extension and duality belong to
later G2-A/B queues, not to the P1–P6 completion claim. In particular the
Eisenstein quotient uses the completion kernel, not the Eisenstein ideal.

## Is G2-C a shorter first path?

No, for the actual endpoint. Its hypotheses include the actual Jacobian,
Hecke action, finite-flat constituents and completion-support quotient.
Mathlib's general cohomology and height tools do not supply admissibility,
uniform bounds in the torsion exponent, Kummer descent, or Mordell–Weil
finite generation for general abelian varieties. Auxiliary l=2 must remain.
Independent algebraic consequences of finite generation can be short, but
assuming finite generation or a uniform bound does not discharge G2-C.
Thus P1–P6 are useful first producers; neither route currently bypasses
the representability and arithmetic source-design gates.

## Validation and release boundary

For every new module: foreground `LEAN_NUM_THREADS=2 lake build MODULE`,
then `lake exe runLinter MODULE` individually; audit all originating
declarations for only `propext`, `Classical.choice`, `Quot.sound`.
New modules and sorted FLT.lean imports only. Before handoff merge
origin/main and build FLT once. Record actual sizes/commits and any open
construction gate in the untracked W1 handoff. Mazur_statement remains
until its unconditional producer and final integration are proved.

## Integration update (2026-10-04)

Fresh origin/main `0d2a816c` added `LineSheafDualEvaluation` after this
audit was committed. Its `LocallyFreeRankOne.dual` and
`lineSheafDualEvaluationIso` discharge P2. W1's independently implemented
`LineBundleDualEvaluation` was removed during integration; P3 now imports
and uses the upstream proof. Thus the final release adds five modules,
not a second dual-evaluation implementation. P1 and P3–P6 are implemented;
P7–P21 remain open. Builds, individual lints, axiom checks and the final
root integration result are recorded in the untracked `BLOCKED.md`.

The next P7 subdivision should first construct the map from affine scheme
Picard classes to `CommRing.Pic` of the actual global-section ring.
`FiniteSchemeInvertibleSections.finiteScheme_sections_invertible` already
contains the affine tensor calculation, but its public statement assumes a
finite scheme over a field. Generalize that calculation using P2 and
`ModuleSheafTensor.affineSectionsEquiv`; use `affineAdjunction` from
`AffineModuleGlobalSections` to prove injectivity. The converse still needs
local trivializations of the tilde sheaf from
`Module.Invertible.exists_finset_free_localization`, and compatibility
with tensor and arbitrary affine pullback. These are proof obligations,
not assumptions to put into a comparison structure.

## Checked release (2026-10-04 22:42 UTC)

At Lean source head `ff86441e`, the five retained modules total 452 physical
lines (107, 61, 82, 92, 110; each below 240). Individual foreground builds
and `lake exe runLinter MODULE` passed. The module-origin axiom audit
checked 90 declarations (24, 14, 16, 14, 22 respectively), including
generated declarations, with only `propext`, `Classical.choice`,
`Quot.sound`. The identity-relative-group, arbitrary-base normalization
and characteristic-two consumer checks compiled.

After merge `3cd5323f` of fresh origin/main `0d2a816c`, the single foreground
`LEAN_NUM_THREADS=2 lake build FLT` passed all 12504 jobs, including
FermatsLastTheorem. Its guarded axiom check still includes
`Mazur_statement` and `sorryAx`. P1–P6 are discharged (P2 reused from main);
P7–P21 and the Mazur endpoint remain open. Reproduction commands and logs
are indexed in the local untracked `BLOCKED.md`; no push was performed.


## W2 implementation and next source split (2026-10-04)

The W1 release sections above describe their historical checks. The current
W2 sources can be checked with the following individual commands; run them
sequentially with `LEAN_NUM_THREADS=2`, never whole-library lint:

| Module (`FLT.Mazur.` prefix) | Mathematical output | Read-only checks |
| --- | --- | --- |
| AffinePicardSections | Invertibility of affine sections; multiplicative map; injectivity by the actual affine counit | `lake build FLT.Mazur.AffinePicardSections`; `lake exe runLinter FLT.Mazur.AffinePicardSections` |
| TildeInvertibleLocal | Principal-open trivializations from the finite localization cover of an invertible module, in arbitrary universes | `lake build FLT.Mazur.TildeInvertibleLocal`; `lake exe runLinter FLT.Mazur.TildeInvertibleLocal` |
| AffinePicardComparison | Multiplicative equivalence with `CommRing.Pic` of actual global sections; naturality for every affine morphism | `lake build FLT.Mazur.AffinePicardComparison`; `lake exe runLinter FLT.Mazur.AffinePicardComparison` |
| RelativePicardPresheaf | Actual functor on `(Over S)ᵒᵖ`, using fiber products and quotient groups | `lake build FLT.Mazur.RelativePicardPresheaf`; `lake exe runLinter FLT.Mazur.RelativePicardPresheaf` |
| AffineModuleCoalgebraDescent | A quasi-coherent sheaf from a faithfully flat scalar-extension coalgebra, with pullback reconstruction respecting the coaction and recovery of canonical data | `lake build FLT.Mazur.AffineModuleCoalgebraDescent`; `lake exe runLinter FLT.Mazur.AffineModuleCoalgebraDescent` |

These five foreground builds and individual lints passed on 2026-10-04.
The per-release untracked `BLOCKED.md` records the final axiom audit, exact
commits and root integration check. Each module is below 240 physical lines.
P7 does not require a finite scheme, a Noetherian base, or characteristic
restrictions. Its group equivalence incorporates tensor compatibility;
`affineEquiv_pullback` proves compatibility with arbitrary affine pullback.
The P8 value remains a presheaf value; no fppf sheafness is asserted.

### P9: faithfully flat line-bundle descent

Source proof: [Stacks, Proposition 35.3.9, tag 023N](https://stacks.math.columbia.edu/tag/023N),
read 2026-10-04. For a faithfully flat map R → A and a cocycle φ on N,
the descended module is the equalizer
`{ n ∈ N | 1 ⊗ n = φ(n ⊗ 1) }`. Faithful flatness and the cocycle equation
prove `A ⊗ M ≅ N`; the source reduces this to the split case after a further
faithfully flat extension. This is an effectiveness proof, not an existence
field to assume.

Mathlib `Algebra/Category/ModuleCat/Descent.lean` proves
`comonadicExtendScalars`. W2 transports this actual equivalence through
`tilde`, obtaining the sheaf and its reconstruction isomorphism in
`AffineModuleCoalgebraDescent`. Its `coefficientIso_coaction` checks
compatibility with the original coalgebra coaction. The input is a module
with counit/coassociativity data; it contains no descended-object witness.

The following leaves remain, each to be split again if it exceeds 240 lines:

| Leaf | Required output | Dependencies |
| --- | --- | --- |
| P9b | Translate a geometric isomorphism between the two pullbacks over `Spec(A ⊗[R] A)`, with diagonal and triple-overlap cocycle equations, into the scalar-extension coalgebra; prove the reverse translation | Affine pullback comparison, tensor associativity, Spec tensor/fiber-product comparison |
| P9c | Prove invertibility descends under faithfully flat scalar extension; one route is descent of finite presentation/projectivity followed by base-change of dual evaluation and reflection of isomorphisms | Finiteness descent, dual base change, faithfully flat reflection |
| P9d | Apply P9c to the descended coefficient module, then P7 to obtain a line bundle with its **specified geometric** descent datum | W2 coalgebra sheaf descent, P9b, P9c |
| P9e | Descend morphisms and isomorphisms compatibly, then glue across affine refinements to obtain the scheme-level stack assertion | P9d, open-cover gluing, base-change coherence |

Mathlib's module-descent file still explicitly marks effective descent for
the scalar-extension pseudofunctor as TODO. Likewise
`CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean` marks its comparison
with geometric `DescentData` as TODO. These are the exact unchecked interfaces;
W2's coalgebra construction does not claim to solve them. P9c is also not a
consequence of the ring Picard map being injective: Picard pullback along a
faithfully flat map need not be injective.

### P15: representability source and dependency boundary

Source: [Stacks, Section 44.6, tag 0B9R](https://stacks.math.columbia.edu/tag/0B9R),
read 2026-10-04, together with [the Picard functor, tag 0B9K](https://stacks.math.columbia.edu/tag/0B9K).
For a smooth projective pointed curve, the source first proves universal
H0 base change, identifies the normalized kernel functor with the relative
Picard sheaf, and constructs an open subfunctor represented by an open of
`Hilb^g`. The universal divisor is normalized along the point; cohomology
and base change identify the locus whose derived pushforward is a line
bundle in degree zero. These open pieces feed the representability proof.

The required proof leaves are: universal H0 comparison; rigidification and
fppf sheaf comparison; existence of the divisor parameter space and universal
divisor; openness and base change of the required cohomology locus; the
universal-divisor/line-bundle bijection; and assembly of the representing
scheme. The existing P6 normalization and W2 P8 presheaf supply only parts
of the inputs. No Hilbert scheme, Jacobian, or abelian variety has been
chosen in place of these proofs. P10–P21 and the unconditional Mazur producer
remain open; this release does not remove `Mazur_statement`.

## W3: tensor cocycles and rank-one descent

The new algebraic interface is `AffineTensorCocycle.Datum R S N`. Its overlap
is an `S`-linear isomorphism `N ⊗[R] S ≃ S ⊗[R] N`; `other_smul` records
the second overlap scalar action, `diagonal` is the diagonal identity, and
`cocycle` is the full three-factor identity, for every `n`, `s`, and `t`.
None of these fields supplies a descended object or an invertibility proof.

| Module (`FLT.Mazur.` prefix) | Proved output | Gate status |
| --- | --- | --- |
| AffineTensorCocycle | Evaluate the overlap at `n ⊗ 1`; prove counit/coassociativity; construct the scalar-extension coalgebra; recover the full overlap from the coaction | Algebraic part of P9b |
| AffineTensorCocycleTransport | Canonical cocycle on scalar extensions and transport along coefficient isomorphisms, with all three datum equations | Algebraic part of P9b |
| AffineTensorCoalgebraComparison | Recover a tensor cocycle from every faithfully flat coalgebra; round-trip recovers the exact original coaction and overlap | Algebraic part of P9b |
| FaithfullyFlatInvertible | Descend finite presentation; commute dual/evaluation with flat base change; reflect evaluation bijectivity by faithful flatness | P9c complete |
| AffineLineCoalgebraDescent | Descended coefficient invertible; actual tilde sheaf locally rank one; compatible morphisms descend functorially and uniquely with the reconstruction square | Coalgebra parts of P9d/P9e |
| AffineTensorDescentMorphisms | Full overlap compatibility iff coaction compatibility; construct the coalgebra morphism from the original overlap-compatible coefficient map | Algebraic morphism interface |

Read-only reproduction: run `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE`
and `LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE` for each row,
sequentially. The W3 local handoff records the checked time, module-origin
axiom audit, commit IDs, physical sizes, consumer checks, and integration
build. No scheme-level descent or representability claim follows from this
table alone.

### W4: geometric projection coordinates and forward diagonal

The double-overlap section comparison is implemented in the following new
modules. Full P9b still requires the triple-overlap comparison and the
reverse construction. The diagonal theorem is a forward implication for
the actual sheaf equation in the tensor-spectrum chart; it is not a proved
equivalence of geometric and tensor descent data.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| AffineOverlapTensor | Identify extension along both tensor-ring inclusions with the ordered coefficient tensors; compute both overlap-ring actions |
| AffineOverlapPullback | Identify actual projection-pullback sections with both tensor modules; give unit formulas, scalar laws, and comparison with the fiber-product projection sheaves |
| AffineGeometricOverlap | Construct the tensor overlap from a sheaf isomorphism; prove first-scalar linearity, second-scalar compatibility, and exact section-map reconstruction; transport an actual fiber-product isomorphism to the chart |
| SchemeModulePullbackUnits | Prove unit normalization for composition, identity, equality, and retractions from adjunction mates; compute affine retraction on scalar multiples |
| AffineOverlapDiagonal | Identify tensor multiplication with the actual diagonal chart; prove diagonal evaluation is tensor contraction and derive `tensorEquiv_diagonal` from `DiagonalCompatible` |

Recheck each module separately with `LEAN_NUM_THREADS=2 lake build MODULE`
and `LEAN_NUM_THREADS=2 lake exe runLinter MODULE`. Never lint the whole
library in this worker's memory cgroup. The W4 handoff records the actual
validation time and commits; these source-level interfaces are the durable
proof artifacts.

Module-level checks completed 2026-10-05 00:14 UTC: the per-module build
and lint commands above passed for all five modules. The W4 axiom audit
checked 99 originating declarations, using only `propext`, `Classical.choice`,
and `Quot.sound`. Full P9b remains unproved for the reasons below.

### Remaining geometric interfaces, in order

1. Compare all three actual triple-overlap projection pullbacks with tensor
   coordinates. The new `comp_unit` and `spec_unit_smul` formulas give
   normalization on unit tensors. Compute the three ring maps explicitly:
   `s ⊗ t ↦ s ⊗ (t ⊗ 1)`, `s ⊗ t ↦ 1 ⊗ (s ⊗ t)`, and
   `s ⊗ t ↦ s ⊗ (1 ⊗ t)`. Prove these are the corresponding scheme maps;
   use the section comparison and scalar generation to derive the full
   `Datum.cocycle` equation, including arbitrary two extra scalars.
2. Construct the geometric overlap back from a tensor isomorphism respecting
   both scalar actions. Prove diagonal and cocycle compatibility in reverse,
   and both round-trips. `tensorEquiv_sections` records exact recovery of
   the original section map; quasi-coherent reconstruction can promote
   section equality to sheaf-map equality. Coherence with the categorical
   fiber-product normalizations must also be proved, not assumed.
3. Transport the existing descended line bundle and reconstruction through
   this full comparison. Recover the **specified** geometric datum using
   `fromCoalgebra_toCoalgebra_overlap`; equality of a Picard class is
   insufficient. This is the remaining geometric part of P9d.
4. Translate compatible geometric maps using `coaction_comm_iff`, descend
   with `descendedModuleMap_unique`, and prove affine-refinement coherence
   before gluing. This is P9e; scheme-level stack descent is still open.
5. Continue P10–P21 in the order above. No representability witness, actual
   `J0(p)`, or Abel–Jacobi-at-infinity producer follows from W4.

Each leaf remains capped at 240 physical lines. None of the new comparison
results removes `Mazur_statement` from the endpoint's axiom dependencies.


## W5: triple pair maps and coefficient-lifting foundations

The following interfaces extend W4. They do not yet construct a full
geometric/tensor descent equivalence.

| Module (`FLT.Mazur.` prefix) | Proved or constructed interface |
| --- | --- |
| AffineTripleOverlapMaps | The three tensor-ring pair maps, their pure-tensor formulas, six coordinate identities, and identification with the actual scheme fiber-product lift |
| AffinePairPullbackSections | The second-projection coefficient equivalence for unequal affine factors, its complete tensor-ring scalar action, and its base-linear form |
| AffineIteratedPullbackSections | Actual composition/equality pullback isomorphism and unit normalization; affine coefficient unit and its naturality; construction of normalized coefficient lifting |

Recheck each module using `LEAN_NUM_THREADS=2 lake build MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, one linter invocation per
module. These exports are the evidence for the table; the W5 handoff records
build, lint, axiom-audit, and integration results with their check times.

At the W5 handoff, the first remaining step was to prove the scalar/unit and
morphism laws of `AffineIteratedPullbackSections.liftSections` without expensive conversion
between additive global sections and module-valued affine sections. The
attempted `liftSections_unit` and `liftSections_map` proofs exceeded the
default kernel budget. A bounded larger-budget attempt was interrupted at
the requested context handoff; it is not a proof result. No enlarged budget
is present in the committed modules.

Then specialize the comparison to all three pair projections, construct the
last-coordinate coefficient chart `S ⊗[R] (S ⊗[R] N)`, and use its injectivity
to derive the full tensor cocycle for every `n`, `s`, and `t`. Those assertions
are not exported by the W5 modules. The reverse overlap reconstruction,
reverse diagonal/cocycle laws, exact round-trips, and coherence with the
categorical fiber-product datum are still the next P9b obligations. P9d,
P9e, representability, actual `J0(p)`, and Abel–Jacobi at infinity follow only
after the earlier interfaces are proved.


## W6: normalized coefficient lifting laws

`AffineCoefficientUnitLaws` gives the generic coefficient unit followed by
an arbitrary sheaf map: evaluation, scalar compatibility, and naturality
under conjugated pullback maps. Its unbundled-ring scalar specialization
keeps the sheaf objects abstract when converting the ring-map coercion.

`AffineIteratedPullbackLaws` proves the previously missing `liftSections_unit`,
`liftSections_smul_unit`, and `liftSections_map`. It also exports the scalar
law on every section, an evaluation lemma, and the equality with the generic
construction. The equality is rewritten explicitly before specialization;
this avoids the kernel timeouts encountered by direct definitional conversion.
Neither module changes the heartbeat budget.

Checked 2026-10-05 using a foreground `LEAN_NUM_THREADS=2 lake build MODULE`
and `LEAN_NUM_THREADS=2 lake exe runLinter MODULE` for each module. The module
builds took 2.4 and 3.1 seconds. `G2_W6_AXIOMS.lean` audited all 12 originating
declarations; only `propext`, `Classical.choice`, and `Quot.sound` occurred.
Re-run those commands and the audit for current evidence. Integration checks
and their timestamps are recorded in the untracked W6 handoff.

At the W6 handoff, the next open item was the three actual pair-transport
coefficient comparisons and the full forward tensor cocycle. The W6 drafts
were unverified and outside the source tree; W7 exports part of this interface below.
Reverse overlap reconstruction, reverse diagonal/cocycle, exact round-trips,
categorical fiber-product coherence, geometric P9d/P9e, and P10–P21 remain
open. These lifting laws do not remove `Mazur_statement` from the endpoint.

## W7: actual pair transports and the last-coordinate chart

`AffineTripleOverlapPullback` constructs all three normalized actual sheaf
isomorphisms and states their sheaf cocycle equation. Its `transport_sections`
proves the coefficient comparison for every pair map, hence for `pair12`,
`pair23`, and `pair13`. The formula uses `mappedUnit` explicitly on each side;
it identifies the transported first chart with the second chart applied to
the specified `AffineGeometricOverlap.tensorEquiv`.

`AffineTripleOverlapCoefficients.lastSections` constructs the additive
isomorphism from `S ⊗[R] (S ⊗[R] N)` to the actual last-coordinate sections.
It uses `AffinePairPullbackSections.linearSections`, a second affine section
comparison, and the actual pullback composition comparison. Bijectivity is
proved from that construction; no injectivity hypothesis is introduced.

These two modules form a 171-line leaf. Neither changes heartbeat or recursion
limits. The module builds, individual module lint, declaration axiom audit,
three concrete pair specializations, and root integration check are recorded
with timestamps in the untracked W7 handoff. Re-run `lake build MODULE`,
`lake exe runLinter MODULE`, and `lake env lean G2_W7_AXIOMS.lean` for current
evidence, using `LEAN_NUM_THREADS=2` and one module at a time.

At the W7 boundary, the scalar-normalized first/second coefficient formulas,
evaluation of `lastSections` on pure tensors, and the full forward tensor
cocycle were open; W8 below advances the first two interfaces. The failed wrappers and normalization experiments are outside the source
tree. In particular, this does not supply `AffineTripleOverlapCocycle.toDatum`.
Next are the reverse overlap, both reverse compatibility equations, exact
round-trips, categorical fiber-product coherence, geometric P9d/P9e, and
P10–P21. `Mazur_statement` has not been removed.


## W8: normalized pair coefficients and iterated chart evaluation

`AffineLiftedOverlapCoefficients` proves `first_normalized` and
`second_normalized`: the actual normalized pair lift sends a pure tensor
to the pair ring map applied to its scalar, acting on the direct coordinate
unit. The intermediate `first_mapped` and `second_mapped` theorems retain
an arbitrary target sheaf. Explicit specialization avoids unfolding the
actual comparison while checking the scalar law.

`AffineTripleOverlapEvaluation` proves `lastSections_outer_apply`, identifies
`linearSections` with the specified `secondSections`, and gives
`lastSections_tmul_iterated`. This last formula evaluates the two coefficient
tensors while retaining the outer section/comparison chain; it does **not**
yet move both scalars through that chain to the direct third-coordinate unit.

The modules contain 78 and 76 lines, respectively (each below the 240-line
leaf cap), with no new axioms or admissions and no limit overrides. Validation
commands are `LEAN_NUM_THREADS=2 lake build MODULE`,
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE` separately for each module,
and `LEAN_NUM_THREADS=2 lake env lean G2_W8_AXIOMS.lean`. The untracked W8
handoff records the checked-at times, results, and concrete consumer checks.

Next: finish scalar normalization of the outer last-coordinate chain, then
combine all three `transport_sections` equations with `CocycleCompatible`
and `lastSections` injectivity to prove the full forward tensor cocycle.
There is still no geometric `toDatum` constructor. Reverse overlap,
diagonal/cocycle and exact round-trips, categorical fiber-product coherence,
geometric P9d/P9e, and P10–P21 follow in the existing order. This work does
not remove `Mazur_statement`.


## W9: a direct third-coordinate chart

`AffineDirectTripleSections` constructs `directSections`, an additive
isomorphism onto coefficients of the actual `coord3` pullback. It rotates
the triple tensor ring so that the restricted third-coordinate scalar
becomes the first scalar, cancels base change, and uses the direct affine
pullback section comparison. `directSections_tmul` gives the fully normalized
pure-tensor formula with scalar `a ⊗ (b ⊗ 1)` and the direct unit.

`AffineDirectTripleEvaluation` identifies this chart on pure tensors with
the normalized `pair23` pullback after the outer scalar, and with the
normalized `pair13` pullback after inserting the middle scalar. Both use
the existing actual composition comparisons and `second_normalized`.

These modules have 90 and 70 lines. Their checks are the per-module
`LEAN_NUM_THREADS=2 lake build MODULE`, separate
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, and the originating-declaration
axiom audit `LEAN_NUM_THREADS=2 lake env lean G2_W9_AXIOMS.lean`. Checked-at
results and commits are recorded in the untracked W9 handoff.

This is an alternative direct chart; equality with W8's iterated
`lastSections` has not been proved. The next step is to extend the two
pure-tensor pair formulas to arbitrary tensors by additivity, then combine
the three `transport_sections` equations and `CocycleCompatible` using
`directSections` injectivity. The general-form prototypes still encounter
instance-matching timeouts in their additive branches. The full forward
cocycle and geometric `toDatum` remain open, followed by the reverse
comparison and the previously listed geometric obligations. No removal
of `Mazur_statement` is claimed.


## W10: arbitrary tensors and first-coordinate balance

`AffineDirectTripleAdditivity` proves the two general pair formulas
`directSections_outer` and `directSections_insertMiddle` for every inner
tensor. Its `sections` chart uses the same restricted coefficient instance
as `firstSections` and `secondSections`. It is constructed from the actual
third-coordinate scalar extension and affine section comparison, and has a
proved pure-tensor evaluation. The tensor-induction arguments are proved
first for abstract additive diagrams, then specialized; this avoids expanding
the sheaf module structures during the induction's kernel check.

`AffineDirectTripleBalance.firstLift_balance` proves the equality of the
normalized first-coordinate lifts along pair12 and pair13 for every
coefficient and both extra scalars. It uses actual `mappedUnit` and
`comparison` terms, followed by commutativity of the two triple scalars.

These modules have 126 and 49 lines. Their validation commands are the
individual `LEAN_NUM_THREADS=2 lake build MODULE`, separate
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, and
`LEAN_NUM_THREADS=2 lake env lean G2_W10_AXIOMS.lean`. Checked-at results,
commits, and the final root-build result are in the untracked W10 handoff.

The first remaining obligation is `transport23_coefficients`: identify the
actual last-pair transport with tensor transport for arbitrary inner tensors.
The attempted pure case encounters a kernel conversion bottleneck between
bundled and unbundled scalar instances; no transport23 theorem from these
experiments is delivered. Combine that identity, first-coordinate balance,
the general pair13 formula, all three `transport_sections` equations, and
`CocycleCompatible` to finish the full tensor cocycle and geometric `toDatum`.
Then construct reverse overlap, diagonal/cocycle, exact round-trips, and
categorical fiber-product coherence before geometric P9d/P9e and P10–P21.
The new chart has not been proved equal to W9's `directSections` or W8's
iterated `lastSections`. No removal of `Mazur_statement` is claimed.

## W11: scaled transport through the actual pair pullbacks

Three further leaves advance the first open W10 item:

| Module | Result | Lines/cap |
| --- | --- | --- |
| `AffineDirectTripleMiddleBalance` | The pair12 second-chart lift and pair23 first-chart lift agree after multiplying by the omitted coordinate scalars | 49/240 |
| `AffineScaledPullbackSections` | Conjugated pullback maps preserve scalar multiples of normalized units; a tensor-ring specialization retains abstract target sheaves | 52/240 |
| `AffineScaledTripleTransport` | Actual normalized transport intertwines scaled coefficient sections for arbitrary pair map, coordinate maps, scalar, and overlap tensor | 67/240 |

The scalar transport proof needs an intermediate tensor-ring specialization
with abstract target sheaves. It aligns the scalar `Semiring` instances before
substituting the concrete coordinate pullbacks, avoiding the kernel conversion
that prevented the direct application of sheaf linearity. Both scalar transport
equations use actual comparison morphisms; the second uses the existing
`tensorEquiv_sections` reconstruction equation.

Validation: separate foreground `LEAN_NUM_THREADS=2 lake build MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE` passed for all three modules on
2026-10-05 at 05:39 UTC. The originating-declaration audit is
`LEAN_NUM_THREADS=2 lake env lean G2_W11_AXIOMS.lean`; checked-at results and
commits are recorded in the untracked W11 handoff.

The full `transport23_coefficients` equation is still open at its join with
`AffineDirectTripleAdditivity.sections`. The pure-tensor attempt exposes a
remaining coefficient-module instance mismatch; even the variable-tensor
composition currently times out during kernel checking. Thus the full forward
cocycle and `toDatum` remain open. The reverse overlap, round-trips, categorical
normalization coherence, geometric P9d/P9e, and P10–P21 remain in the same order.
No geometric datum, representability witness, or Jacobian witness is assumed,
and no removal of `Mazur_statement` is claimed.


## W12: direct-chart join and pure last-pair transport

`AffineDirectTripleTransport.transport23_outer` joins the scaled pair23
transport to `AffineDirectTripleAdditivity.sections` for every overlap tensor.
`AffineDirectTriplePureTransport.transport23_tmul` combines that join with
`middleLift_balance`, proving actual last-pair transport on each pure inner
tensor. Its `outer_smul` lemma aligns the scalar notation with an abstract
sheaf target; the explicit tensor input keeps the coefficient instances fixed.
Both concrete results use the existing actual sheaf maps and comparisons.

`AffineTensorTransportAdditivity.transport_coefficients` proves the abstract
additive extension from pure tensors to arbitrary coefficient tensors. Its
specialization to the actual sheaf maps is a separate, unfinished obligation:
the attempted specialization still incurs expensive conversions between
bundled ring carriers and the triple tensor ring, and between expanded
pullbacks and the `coordinate` abbreviation. The generic induction theorem
alone does not establish the concrete `transport23_coefficients` equation.

Validation on 2026-10-05: individual foreground builds and one-module lints
for these three modules; originating-declaration axiom audit via
`LEAN_NUM_THREADS=2 lake env lean G2_W12_AXIOMS.lean`. Checked-at evidence,
commits, and the post-merge root-build result are in the untracked W12 handoff.
The remaining order is the concrete additive specialization, full forward
cocycle and `toDatum`, reverse overlap and round-trips, categorical
normalization, geometric P9d/P9e, then P10–P21. `Mazur_statement` remains.


## W13: concrete additive maps and a bundled generator criterion

`AffineTripleCoefficientMaps` defines `coefficientTransport`, the actual
pair23 section map after the scaled pair12 lift, and `coefficientAction`,
the last-slot tensor action followed by the direct third-coordinate chart.
`coefficientAction_apply` evaluates the latter on every tensor;
`coefficientAction_tmul` evaluates it on generators. The pure evaluation
uses an abstract tensor calculation before applying the actual section
chart, avoiding reduction of the concrete sheaf construction.

`AffineTripleCoefficientExtensionality.coefficientMaps_eq_iff` reduces
identity of these two actual additive maps to their pure-tensor values.
`coefficientMaps_eq_of_tmul` and
`coefficientTransport_coefficients_of_tmul` use the evaluated right-hand
side. They require a generator equation for the **bundled** transport map.
They do not establish that hypothesis from the existing **unbundled**
`transport23_tmul` theorem.

The first ordered item therefore remains open. The next step is an
evaluation bridge from `coefficientTransport` to the unbundled section
formula, then use `transport23_tmul` to discharge the generator hypothesis.
The attempted bridge elaborates after coercion simplification but still
hits a kernel timeout; no failed bridge is imported. Full forward cocycle,
`toDatum`, reverse overlap and round-trips, categorical normalization,
geometric P9d/P9e, and P10–P21 remain in their previous order.
`Mazur_statement` has not been removed.

Checked at 2026-10-05T07:01:09.437602+00:00: separate foreground builds and module-only lints
passed for both 81-line modules. Recheck with
`LEAN_NUM_THREADS=2 lake build FLT.Mazur.AffineTripleCoefficientMaps` and the
corresponding `AffineTripleCoefficientExtensionality` target, then run
`lake exe runLinter MODULE` once for each module. The axiom audit and
post-sync root-build evidence are in the untracked W13 handoff.


## W15: arbitrary coefficients, the full cocycle, and the forward datum

`AffineDirectTripleCoefficients.transport23_coefficients` extends the actual
last-pair section formula to every coefficient tensor. It uses tensor induction
with the sheaves kept abstract until the scalar instances have been fixed.
This directly proves the unbundled equation requested after W13; the auxiliary
bundled `coefficientTransport_apply` bridge is not needed by this route.

`AffineGeometricTensorCocycle` evaluates the geometric `CocycleCompatible`
equation on sections, combines the first-coordinate balance and the scaled
pair12/pair13 transports, and proves `tensorEquiv_cocycle` for every `n,s,t`.
The injective direct third-coordinate chart detects the resulting tensor
identity. Explicit tensor type ascriptions keep the coefficient instances
aligned; the composed section formulas use the expanded pair12/pair13 maps.

`AffineGeometricTensorDatum.toDatum` constructs the actual `Datum R S
(coefficients S M)` from a geometric overlap, `DiagonalCompatible`, and
`CocycleCompatible`. Its four fields use the specified tensor isomorphism and
proved scalar, diagonal, and cocycle equations. `toDatum_overlap_sections`
reconstructs the given sheaf map on sections, and `toDatum_coaction_apply`
identifies the coaction at the unit tensor factor. No descended object or
Jacobian witness is a parameter. This forward construction uses the direct
chart throughout and does not require an older iterated-chart comparison.

The next obligation is the reverse geometric overlap from a tensor isomorphism
respecting both scalar actions, followed by its diagonal/cocycle equations,
exact round-trips, and categorical fiber-product normalization coherence.
Geometric P9d/P9e and P10–P21 follow in their previous order. The forward datum
alone does not remove `Mazur_statement`.

The three modules have 89, 120, and 58 lines (cap 240 each). The coefficient
specialization, full cocycle, and datum constructor each scope `maxRecDepth
2048` to one declaration; heartbeat and memory limits are unchanged.
Validation commands are individual `LEAN_NUM_THREADS=2 lake build MODULE`,
individual `lake exe runLinter MODULE`, the declaration audit in the untracked
`G2_W15_AXIOMS.lean`, and the post-merge `LEAN_NUM_THREADS=2 lake build FLT`.
The checked-at receipts and remaining-work handoff are in the untracked
`MAZUR_G2_W15_DONE.md`; this paragraph is not a completion claim for G2.

## W16: reverse comparison and affine geometric descent

The reverse comparison is now implemented by the modules below. Recheck each
with `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and then
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`, one module at a time.
The declarations themselves are the evidence for the interfaces in this table.

| Modules (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| AffineSectionsReconstruction, AffineTensorSectionIso, AffineReverseGeometricOverlap | Reconstruct the actual overlap from both tensor scalar actions; exact tensor/overlap round-trips |
| AffinePullbackHomExt, AffineReverseOverlapDiagonal | Detect maps on unit sections; recover the geometric diagonal from contraction |
| AffinePairUnitTransport, AffineTripleUnitCoefficients, AffineReverseOverlapCocycle | Recover the actual geometric cocycle from its unit-factor tensor equation; equivalence with the full tensor cocycle |
| AffineGeometricDatumComparison | Tensor data reconstruct geometric diagonal and cocycle equations, with exact round-trips |
| AffineFiberProductOverlap | Mutually inverse normalization and reconstruction for actual categorical fiber-product overlaps |
| AffineGeometricDescent | Construct the descended affine sheaf and pullback reconstruction; recover the specified overlap via `fromCoalgebra_toCoalgebra_overlap`; invertible coefficients give a line bundle |
| AffineOverlapMapSections, AffineGeometricMapComparison | Naturality of both coefficient charts; equivalence between actual geometric squares and tensor compatibility |
| AffineCoalgebraSheafNaturality, AffineFaithfullyFlatPullbackFaithful | Naturality of reconstruction and faithfulness of pullback on tilde sheaves |
| AffineGeometricDescentMorphisms | Descend compatible geometric morphisms and isomorphisms; prove the actual sheaf reconstruction square and uniqueness of its descended map |

The reverse-cocycle memory issue is avoided by specializing the scalar ring
while source and target sheaves remain abstract. Specializing directly to
concrete pullback sheaves forces expensive definitional comparisons. Small
intermediate lemmas keep the final reverse cocycle within ordinary resource
limits; no tensor-product implementation is unfolded in that proof.

This supplies affine geometric object reconstruction and uniquely determined
morphism reconstruction. The line-bundle theorem currently takes invertibility
of the affine coefficient module as its hypothesis. Scheme-level P9e still
requires compatibility under affine refinements and gluing, including coherence
of the chosen reconstruction isomorphisms. P10–P21 (relative Picard comparison,
cohomology/base change, representability, and the actual modular-curve/Jacobian
producer) remain separate obligations. These results do not remove
`Mazur_statement` from the endpoint.

## W17: affine refinement reconstruction and recognition

The following modules develop the first remaining W16 item. Each can be checked
with `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` followed by
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`, one module at a time.
Declaration-level axiom receipts and checked-at validation are in the untracked
`G2_W17_*_AXIOMS.log` and `MAZUR_G2_W17_DONE.md` handoff.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| AffineRefinementPullback | Natural comparison of iterated pullbacks around a commutative affine square; transport of reconstruction and its map square |
| AffineQuasicoherentPullbackFaithful | Faithfully flat pullback detects maps between arbitrary affine quasi-coherent sheaves and verifies proposed inverses |
| AffineDescentRefinementReconstruction | Restrict a descended sheaf and its reconstruction; restricted descended maps satisfy the refined square and are uniquely determined by it |
| AffineGeometricDescentComposition | Actual overlap compatibility is closed under identities and composition; descended maps and isomorphisms preserve composition |
| AffineCoalgebraDescentRecognition | A canonical-coalgebra isomorphism identifies a candidate module with the descended module, uniquely with its specified coefficient reconstruction; the same square holds on tilde sheaves |
| AffinePullbackCoefficientRecognition | Lifting the scalar-extension coefficient chart recovers the given geometric reconstruction exactly |
| AffineGeometricDescentRecognition | An explicit coaction equation on a candidate's coefficient chart constructs its isomorphism to the descended sheaf, with exact reconstruction and uniqueness |
| AffineDescentRefinementComparison | Conditional comparison between restriction and separately descended refined data; comparison is natural for compatible maps |
| SchemeOverlapRefinement | Restrict actual categorical overlap isomorphisms along a commutative refinement square; preserve compatible maps and prove the defining conjugation square |
| AffineGeometricOverlapRefinement | Normalize that restricted categorical overlap on the refined tensor-spectrum chart, with exact recovery of the categorical overlap |
| SchemeOverlapRefinementCoherence | Maps of double overlaps preserve the diagonal, identity refinements, and composition as actual scheme-morphism equalities |

The comparison hypothesis `AffineGeometricDescentRecognition.CoactionCompatible`
is the equation intertwining the canonical scalar-extension coaction with the
specified datum through the reconstruction's coefficient chart. It is not yet
proved for the constructed refined overlap. In particular, the conditional
comparison does not finish affine-refinement descent or scheme-level P9e.
The last row concerns maps of schemes; it does not assert preservation of the
sheaf overlap's diagonal or cocycle laws.

The W18 checkpoint below advances this list. At the W17 checkpoint the order was:

1. Prove that `AffineGeometricOverlapRefinement.overlap` preserves the geometric
   diagonal and cocycle equations, and bundle it as the refined `Data`. The
   scheme maps and projection comparisons are in `SchemeOverlapRefinement`;
   its companion coherence module supplies the diagonal and composition maps.
2. Prove `CoactionCompatible` for `AffineDescentRefinement.reconstruction` and
   this constructed datum. Apply `comparisonIso` and its reconstruction equation;
   prove identity and composite coherence of the comparison isomorphisms by
   faithful-flat uniqueness, including the pullback composition comparisons.
3. Glue the objects and maps across affine covers to finish scheme-level P9e.
4. Supply the geometric locally-free-rank-one to coefficient-invertibility
   bridge before invoking affine line-bundle descent on geometric inputs.
5. Continue P10–P21 as already ordered above. None of these modules removes
   `Mazur_statement` or constructs the actual modular curve/Jacobian producer.


## W18: sheaf diagonal preservation and cocycle transport

The diagonal part of W17 item 1 is proved by
`AffineGeometricOverlapRefinement.overlap_diagonal`. Its hypothesis is the
original geometric `Data`; the refined diagonal equation is not an additional
assumption. The cocycle infrastructure below does not yet discharge the
refined affine cocycle or construct the refined `Data`.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| SheafPullbackPathComparison | Normalized path comparison, associativity, and both unit laws |
| SchemeOverlapDiagonalChart | Actual sheaf diagonal equations survive chart normalization |
| SheafPullbackRetractionSquare | Projection and diagonal squares commute with sheaf retraction comparisons |
| SchemeOverlapRefinementDiagonal | The categorical overlap refinement preserves the sheaf diagonal equation |
| SchemeOverlapDiagonalDetection | A chart containing the diagonal detects its sheaf equation |
| AffineFiberProductDiagonal | Equivalence of affine and categorical diagonal laws; reconstruction preserves them |
| AffineGeometricOverlapRefinementDiagonal | The constructed refined affine overlap has its geometric diagonal law |
| SchemeOverlapTransportComposition | Successive normalized overlap transports agree with transport along the composite |
| SchemeOverlapCocycleChart | Double-overlap chart normalization preserves and detects cocycles on a common triple test scheme |
| SchemeOverlapCocyclePullback | Normalized pullback preserves composition and restricts a cocycle to another triple test scheme |
| SchemeOverlapBaseChange | Changing the coordinate sheaf base commutes with pair transport and preserves composition |
| SchemeOverlapRefinementCocycle | Restriction preserves a cocycle on specified composite pair maps; its restriction equals the existing categorical refinement |
| AffineFiberProductPairTransport | Pair maps from the affine triple overlap to the categorical double overlap, their projection squares, and coordinate sheaf transports |

`SchemeOverlapRefinementCocycle.restrict_cocycle` takes the original overlap's
cocycle on the composite pair maps from the refined triple test scheme.
It does not assume the restricted overlap's cocycle. To apply it to affine
refinement, construct the map from the refined affine triple overlap to the
original one, prove its coordinate and pair squares, and pull back the original
cocycle using `SchemeOverlapCocycleChart.pullback_cocycle`.

Continue in this order:

1. Compare affine pair transport with `AffineGeometricOverlap.fiberProductTransport`,
   then complete the affine triple-overlap refinement and cocycle comparison.
   Prove `AffineGeometricOverlapRefinement.overlap` has the cocycle and combine
   it with `overlap_diagonal` to produce the refined `AffineGeometricDescent.Data`.
2. Prove `CoactionCompatible` for the W17 reconstruction and the constructed
   refined datum, then comparison identity/composition coherence by uniqueness.
3. Glue across affine covers to finish P9e.
4. Bridge geometric locally-free rank one to invertible affine coefficients.
5. Continue P10–P21, including the actual modular curve and Jacobian producers.

Validation is reproducible per module with foreground
`LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`.
The untracked W18 handoff records checked-at receipts, declaration-level axiom
checks, source caps, commits, main ancestry, and the required root build.
No result here removes `Mazur_statement` from the endpoint.


## W19: actual refined data and reconstruction-chart data

The first open W18 item is complete. `AffineGeometricOverlapRefinement.data`
constructs the refined `AffineGeometricDescent.Data` from the original datum
and the commutative ring square. Both equations are proved: the existing
W18 diagonal law and the new `overlap_cocycle`. No refined equation is an
additional hypothesis.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| AffinePullbackNormalization | Objectwise pullback conjugation equals general scheme normalization |
| AffineFiberProductCocycle | Affine pair transport and the categorical fiber-product cocycle agree |
| AffineTripleOverlapRefinement | Double and triple tensor ring maps, with all three coordinate squares |
| AffineTripleOverlapRefinementSquares | Actual triple-spectrum map and all three categorical pair squares |
| SchemeOverlapRefinementTripleCocycle | Commuting triple-overlap squares preserve the original cocycle under restriction |
| AffineFiberProductCocycleChart | The categorical affine cocycle equals the general scheme predicate on its actual maps |
| AffineFiberProductRefinementCocycle | Apply those squares to preserve the actual affine categorical cocycle |
| AffineGeometricRefinementData | Construct the refined geometric datum with its proved diagonal and cocycle laws |
| AffineCoefficientChartDatum | A coefficient reconstruction chart transports canonical tensor data and intertwines coactions |
| AffineGeometricChartDatum | Construct actual geometric chart data and prove its reconstruction coaction compatibility |

The last two modules start W18 item 2. `chartData_compatible` concerns the
constructed `chartData`, not the actual datum `AffineGeometricOverlapRefinement.data`.
Proving that these two data agree for `AffineDescentRefinement.reconstruction`
remains necessary before applying the W17 refinement comparison unconditionally.
The interrupted uniqueness attempt is retained outside FLT/ and is not a result.

Continue in this order:

1. Identify the actual refined overlap with the geometric datum determined by
   its reconstruction's coefficient chart. A missing intermediate comparison
   identifies the geometric overlap of a pullback sheaf with its canonical
   coefficient datum, and proves that comparison respects refinement squares.
   Prove `CoactionCompatible` for the actual refined datum; apply W17 comparison
   and reconstruction, then prove identity/composition coherence by uniqueness.
2. Glue the objects and maps across affine covers to finish P9e.
3. Bridge geometric locally-free rank one to invertible affine coefficients.
4. Continue P10–P21, including the actual modular curve and Jacobian producers.

Read-only validation commands remain the per-module build, single-module
linter, and originating-module axiom audit. The untracked W19 handoff records
checked-at receipts and the root build after merging main. The endpoint check
`rg -n Mazur_statement FLT/Assumptions/Mazur.lean FermatsLastTheorem.lean`
still finds the Mazur assumption; this checkpoint does not remove it.


## W20: canonical reconstruction recognition (2026-10-05)

The coefficient/geometric comparison left open in W19 is now proved.
`AffineCanonicalOverlapRecognition.coactionCompatible_iff_canonical_overlap`
identifies coaction compatibility with equality of the specified geometric overlap
and the canonical pullback overlap transported through the reconstruction chart.
`chartData_val_eq_canonical_overlap` identifies the tensor-constructed chart datum
with that actual geometric overlap.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| AffineTensorCoactionRecognition | A coefficient coaction determines its tensor datum |
| AffineGeometricChartRecognition | A chart has a unique compatible geometric datum |
| AffineReconstructionCoefficientChart | Compute the chart of a lifted module reconstruction |
| AffineGeometricReconstructionCompatibility | The original effective reconstruction is compatible; its chart recovers the original datum and recognition is the identity |
| AffineGeometricCoactionUnits | Compatibility is equivalent to the actual overlap equation on reconstructed base unit sections |
| SchemePullbackOverlap | Construct the canonical geometric overlap and prove its unit section equation |
| AffineOverlapUnitDetection | Reconstructed base unit sections determine arbitrary geometric overlaps, without diagonal or cocycle hypotheses |
| AffineCanonicalOverlapRecognition | Coaction compatibility is precisely equality with the canonical geometric overlap |
| SchemePullbackOverlapNormalization | Normalization along an overlap map preserves the canonical overlap |

The W18/W19 refinement obligation is still open. In particular, this checkpoint
does **not** prove `CoactionCompatible` for
`AffineGeometricOverlapRefinement.data` and `AffineDescentRefinement.reconstruction`.
The original reconstruction theorem concerns the original datum, before refinement.

Continue with the remaining geometric comparison:

1. Prove canonical overlaps commute with the change of base sheaf and with the
   reconstruction square. Combine `SchemePullbackOverlap.normalize_overlap`,
   `SchemeOverlapBaseChange.normalize_baseChange`, and
   `SheafPullbackPathComparison.comparison_assoc` for the two projection paths.
2. Apply that result to the actual affine refinement and its `squareIso`, including
   the tensor-spectrum/fiber-product chart conversions. Use
   `coactionCompatible_iff_canonical_overlap` to obtain the missing refined
   `CoactionCompatible` theorem. The original overlap is canonical by
   `reconstruction_compatible` and the same equivalence.
3. Apply W17 `comparisonIso`, then prove identity/composition coherence by faithful
   pullback uniqueness. Glue across affine covers to finish P9e.
4. Supply locally-free-rank-one to invertible coefficients, then continue P10–P21
   and the actual modular curve/Jacobian producers. G1 and track D remain separate.

Validation is reproducible with per-module `lake build`, per-module
`lake exe runLinter`, and originating-module axiom audits. The untracked W20
handoff records checked-at receipts and the required post-merge root build.
The endpoint check remains `rg -n Mazur_statement FLT/Assumptions/Mazur.lean
FermatsLastTheorem.lean`; these modules do not remove that assumption.


## W21: compatibility with the actual affine refinement (2026-10-05)

The first two remaining W20 items are proved. Canonical geometric overlaps
commute with the reconstruction square, and both directions of the actual
categorical fiber-product/tensor-spectrum chart preserve them.
`AffineGeometricDescentRecognition.refinement_compatible` proves coaction
compatibility for `AffineGeometricOverlapRefinement.data` and the transported
reconstruction. It needs compatibility only for the original chart.
`AffineDescentRefinement.effective_reconstruction_compatible` supplies that
original compatibility for the effective reconstruction, so its conclusion has
no coaction-compatibility hypothesis.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| SchemePullbackSquare | Normalized paths commute with a scheme square |
| SchemePullbackOverlapSquare | Base change identifies canonical overlaps across the square |
| SchemeOverlapConjugation | Normalization preserves arbitrary reconstruction charts |
| SchemeReconstructionOverlapSquare | Base change transports the full reconstruction chart |
| SchemeCanonicalOverlapRefinement | Actual categorical refinement preserves canonical overlaps |
| AffineCanonicalOverlapChart | Canonical overlaps agree in both affine chart directions |
| AffineRefinementCoactionCompatibility | Actual refined data and transported charts are coaction-compatible |
| AffineEffectiveRefinementComparison | Effective comparison, reconstruction equation, and uniqueness |
| SchemeCanonicalOverlapNaturality | A reconstruction square intertwines canonical scheme overlaps |

`effectiveComparisonIso` now compares restriction of effective descent with
effective descent of the actual refined datum, without an extra compatibility
assumption. Its reconstruction equation and uniqueness are proved.
This completes the object comparison portion of W20 item 3.

Continue in this order:

1. Finish affine map compatibility and naturality. The scheme-level theorem
   `SchemePullbackOverlap.chartOverlap_compatible` is proved. Applying it through
   `coactionCompatible_iff_canonical_overlap` to the affine `MapCompatible`
   statement still needs a smaller kernel-checkable proof. The W21 attempt
   elaborated but exceeded the default kernel limit; neither that attempt nor
   the dependent effective-naturality wrapper is a validated result. Both are
   retained as untracked WIP files outside the library.
2. Prove identity/composition coherence of `effectiveComparisonIso`, using its
   reconstruction equation and `effectiveComparisonIso_unique`. Include the
   actual identifications of the sheaves and geometric data under successive
   refinement; coherence of the overlap scheme maps alone is insufficient.
3. Glue the objects and maps across affine covers to finish P9e.
4. Supply locally-free-rank-one to invertible coefficients, then continue
   P10–P21 and the actual modular curve/Jacobian constructions. Keep G1 and
   track D separate.

Checks: individual `lake build FLT.Mazur.MODULE`, single-module
`lake exe runLinter FLT.Mazur.MODULE`, and originating-module axiom audits.
The untracked W21 handoff records checked-at receipts, memory measurements,
and the root build after merging main. Re-run `python3 G2_W21_SOURCE_CHECK.py`
for the local receipt. The endpoint source check remains
`rg -n Mazur_statement FLT/Assumptions/Mazur.lean FermatsLastTheorem.lean`;
this checkpoint does not remove the Mazur assumption or finish P9e.


## W22: affine naturality and effective identity coherence (2026-10-05)

W21 remaining item 1 is proved. A reconstruction square between coaction-compatible
charts implies `MapCompatible`. Applying this to the effective reconstruction proves
compatibility of the actual refined map and naturality of `effectiveComparisonIso`,
without any extra compatibility hypothesis on that refined map.

For item 2, identity coherence is proved uniformly for refinement maps `a` and `b`
whose spectrum maps are identities. `identityData_compatible` intertwines the actual
refined datum with the original datum using the cover unit chart. `identityDescentIso`
descends that chart, and `effectiveComparisonIso_identity` identifies its composite
with effective comparison as the base unit chart. The identity conditions are
`Spec.map a = 𝟙 _` and `Spec.map b = 𝟙 _`; the original cover is faithfully flat.

Scheme-level composition coherence is also proved, including reconstruction maps
and the actual base and cover pullback composition charts. Its affine specialization
and comparison of the actual successive-refinement data remain open.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| SchemeCanonicalMapRecognition | Equality with canonical overlaps transports map compatibility |
| AffineCanonicalMapCompatibility | A compatible reconstruction square implies `MapCompatible` |
| AffineEffectiveRefinementNaturality | Actual refined maps are compatible; effective comparison is natural |
| SchemePullbackSquareIdentity | Normalized square comparisons and reconstruction respect units |
| SchemePullbackIdentityCharts | Unit charts with explicit source and target sheaves |
| SchemeRefinementReconstruction | Reconstruction charts with explicit iterated-pullback endpoints |
| SchemePullbackSquareComposition | Composition coherence of squares and reconstructed charts |
| AffineRefinementIdentity | Affine reconstruction respects unit charts for identity spectrum maps |
| AffineEffectiveRefinementIdentity | Actual identity-refined data and effective comparison respect units |

Continue in this order:

1. Specialize `SchemePullbackSquare.squareIso_composition` and
   `reconstruction_composition` to two affine refinement squares. Include the
   spectrum map comparison for composite ring maps and both sheaf pullback charts.
   The explicit-endpoint `reconstructionChart` can help control conversions.
2. Use `mapCompatible_of_reconstruction` to identify the actual successively refined
   datum with the datum refined along the composite square. Descend that chart and
   prove composition coherence of `effectiveComparisonIso` by reconstruction
   uniqueness. Identity coherence and naturality are already available.
3. Glue objects and maps across affine covers to finish P9e.
4. Supply locally-free-rank-one to invertible coefficients, then continue P10–P21
   and the actual modular curve/Jacobian constructions, separately from G1 and track D.

Checked on 2026-10-05 with individual `lake build FLT.Mazur.MODULE`, single-module
`lake exe runLinter FLT.Mazur.MODULE`, and originating-module axiom audits. The
untracked W22 handoff records exact timestamps, memory measurements, commits, and
post-merge root-build receipts; `python3 G2_W22_SOURCE_CHECK.py` reruns its local checks.
The endpoint check is `rg -n Mazur_statement FLT/Assumptions/Mazur.lean
FermatsLastTheorem.lean`; P9e and removal of the Mazur assumption remain open.

The direct wrapper specializing unit coherence to literal identity ring maps
exceeded the memory guard and is retained only as untracked WIP. The accepted
uniform identity theorem has been checked by Lean's kernel at the default limits.
No library declaration depends on that rejected wrapper.


## W23: actual affine composition charts (2026-10-05)

W22 remaining item 1 is proved. `AffineRefinementPullback.compositionChart`
includes the actual equality `Spec.map (a ≫ c) = Spec.map c ≫ Spec.map a`.
Both `squareIso_composition` and `reconstruction_composition` include the base
and cover charts for two arbitrary commutative affine squares.

Item 2 is partially proved. `compositionData_compatible` derives compatibility
of the actual successively refined datum and the composite-refined datum from
compatible reconstruction, using the actual cover composition chart.
`compositionDescentIso` descends that chart; its reconstruction theorem is
proved. `effectiveComparisonIso_reconstruction_twice` proves that restricting
the first effective comparison identifies the second reconstruction with the
successively restricted original chart.

| Module (`FLT.Mazur.` prefix) | Proved interface |
| --- | --- |
| SchemePullbackCompositeCharts | Square and reconstruction composition with specified composite maps |
| SchemePullbackCompositeRecognition | Transport through named charts with explicit object endpoints |
| AffineRefinementComposition | Actual affine base/cover charts and composition of reconstruction |
| AffineRefinedCompositionCompatibility | The cover composition chart intertwines actual refined data |
| AffineRefinementReconstructionMap | Refinement preserves maps identifying two reconstructions |
| AffineEffectiveCompositionChart | Descended cover chart and its reconstruction equation |
| ReconstructionComposition | General categorical reconstruction-path calculations |
| AffineEffectiveCompositeReconstruction | The twice-refined effective reconstruction square |

The final `effectiveComparisonIso` composition equality is **not proved**.
The attempted full equality and a separate successive-path reconstruction
lemma elaborated but exceeded the default kernel budget. These attempts are
untracked diagnostics outside `FLT/` and are not imported. No resource limit
was increased. General categorical factoring alone did not resolve this cost.

Continue in order:

1. Finish the effective composition equality using the accepted actual-data
   comparison and twice-refined reconstruction. First isolate the expensive
   conversion in the successive-path reconstruction; consider explicit-endpoint
   wrappers for the composite effective maps before applying reconstruction
   uniqueness. Do not assume compatibility or the composition equation.
2. Assemble the actual affine descent charts into `ModuleSheafGluing.Data`,
   prove its transitions/cocycle, and glue objects and maps to finish P9e.
   Existing `ModuleSheafGluing` and `ModuleSheafMorphismGluing` supply generic
   gluing. Connecting the actual affine charts to this interface remains open.
3. Supply locally-free-rank-one to invertible coefficients, then P10–P21 and
   the modular curve/Jacobian constructions, separately from G1 and track D.

Validation can be rechecked with `python3 G2_W23_SOURCE_CHECK.py` in the worker
checkout. It checks committed source, the 240-line module and 100-character
line caps, build/lint/axiom/probe receipts, root imports, and the post-merge root
build. The untracked W23 handoff records the check timestamp and commits.
`rg -n Mazur_statement FLT/Assumptions/Mazur.lean FermatsLastTheorem.lean`
checks the endpoint: the Mazur assumption remains; P9e remains open.
