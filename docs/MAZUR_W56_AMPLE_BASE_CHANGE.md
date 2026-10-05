# W56: relative ampleness locality and arbitrary base change

The first remaining W55 bridge is implemented. `RelativeAmple.baseChange`
starts with `RelativeAmple f L` and local rank one of `L`; for every scheme map
`g : T ⟶ S`, it proves `RelativeAmple (pullback.snd f g)` for the actual pullback
of `L`. Unfolding that conclusion gives a positive-power closed projective
presentation on **every affine open of T**. Neither base is required to be
affine, Noetherian or reduced. No global presentation is an input.

`GeneralizedEllipticCurve.FiniteSubgroup.IsAmple.baseChange` applies this to the
actual subgroup Cartier divisor. It assumes only that the original subgroup
is ample. Its proof uses the existing canonical ideal comparison and the
positive divisor-line pullback isomorphism.

## Proof and scope

A finite affine cover of a quasi-compact separated scheme and its pairwise
intersections compute quasi-coherent sections as an equalizer. Localization
commutes with both finite products and this kernel, so a section on a principal
open has a global numerator over an arbitrary ring. An extra scalar factor
makes its generator open exactly the original local generator open.

This proves principal-open locality for section ampleness. On an affine new
base, principal neighborhoods map into affine opens of the original base.
Affine pullback makes their restrictions ample; principal-open locality glues
them. Apply this separately to every affine open of an arbitrary new base.

The section-ampleness locality and general base-change theorems are for
**separated morphisms**. Base-open locality also assumes quasi-compactness and
that the coefficient is a line bundle. These are available for proper families.
`RelativeAmple` itself implies properness, so its base-change theorem and the
subgroup theorem need no extra separatedness or properness hypothesis.
The affine-original-base theorem does not require separatedness.

`relativeAmple_of_base_neighborhoods` transports the locality result to the
closed-presentation predicate on proper families. The input neighborhoods may
be arbitrary base opens; they need not form a finite cover or be affine.

## Modules

All leaves are new modules with at most 240 lines, including headers.

| Module | Result |
| --- | --- |
| `AmpleAffineBase` | Affine restriction, scheme-isomorphism invariance, affine-base comparison |
| `RelativeAmpleAffineBaseChange` | Arbitrary new base when the original base is affine |
| `RelativeAmpleRestriction` | Restriction to every base open |
| `SectionBaseLocalization` | Actual global section localization by a base function |
| `SectionGeneratorScalar` | Exact generator open of a scalar multiple |
| `PrincipalSectionExtension` | Global numerators on principal opens; invertible sheaves are finitely presented |
| `PrincipalGeneratorExtension` | Global extension with the exact local generator locus |
| `AmplePrincipalLocality` | Gluing ampleness from principal neighborhoods |
| `AmpleCartesianAffineOpen` | Pulled-back ample sections on affine cartesian pieces |
| `RelativeSectionAmpleBaseChange` | Arbitrary base change for separated section-ample families |
| `RelativeAmpleBaseChange` | Closed power presentations on every affine new-base open |
| `GeneralizedCurveAmpleBaseChange` | Arbitrary base change of actual ample finite subgroups |
| `RelativeSectionAmpleLocality` | Base-open locality and proper-family presentation locality |

## Remaining boundary

This does not prove general fppf descent of ampleness. Pulling back along a
cover is now proved; reflecting ampleness along that cover remains a separate
argument. The arbitrary-base fibre-to-neighborhood theorem also remains: it
requires the finite-type approximation and invertible-sheaf descent described
in W52 contracts L1–L2. No Noetherian-only replacement is used.

The componentwise degree/support theorem and ample-degree criterion in F1–F3
remain. Thus the A6 fibre criterion, A7 moduli quotient/presheaf, and A8
rational-point level construction are not claimed here. The Mazur-removal
endpoint remains open.

## Validation commands

For each listed module, separately:

```text
LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE
LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE
```

The untracked W56 audit enumerates every declaration originating in these
modules and rejects any axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. Consumers check the unrestricted base-change and subgroup
contracts, presentations on an arbitrary affine new-base open, locality, and
a `ZMod 4` original base. The untracked handoff records results, timestamps,
commits and the post-main-merge root build.
