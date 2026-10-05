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
