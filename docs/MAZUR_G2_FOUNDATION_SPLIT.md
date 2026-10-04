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
| P7 | Identify affine scheme line bundles with invertible ring modules, compatibly with tensor/pullback | P4, affine module equivalence | Needs comparison proof |
| P8 | Build the relative presheaf on `Over S` using actual fiber-product pullbacks and prove its composition laws | P5 | Needs cartesian-square assembly |
| P9 | Construct line-bundle descent along faithfully flat affine maps; prove effectiveness | P7 | Needs source-level descent subdivision |
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
