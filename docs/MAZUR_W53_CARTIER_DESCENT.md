# W53: global Cartier descent and the ampleness boundary

The global Cartier obligation from W52 is proved by
`GeneralizedEllipticCurve.FiniteSubgroup.IsCyclic.relativeEffectiveCartier`.
Its only input beyond the finite subgroup is `H.IsCyclic`; no finite-generation,
finite-presentation, stalk-generator, or Cartier-neighborhood hypothesis is added.
The overall Mazur-removal goal is still open.

## Implemented proof chain

Every new module below is capped at 240 lines. The untracked W53 build, linter,
consumer, axiom-audit and source-check artifacts record the checked state and
local commits. Recheck builds with `LEAN_NUM_THREADS=2 lake build MODULE` and
linters with `lake exe runLinter MODULE`, one module at a time.

| Leaf | Module | Mathematical result |
| --- | --- | --- |
| D3c algebra | FlatIdealTensor | Tensor extension of the actual ideal inclusion identifies with ideal extension under flatness; faithfully flat finite-presentation descent for ideals |
| D3c sections | IdealModuleAffineTensor | Compatible affine opens give tensor extension of actual ideal-module sections; pure-tensor inclusion formula; affine faithfully flat descent |
| D3a | IdealCartierNeighborhood | A localized rank-one ideal basis spreads using Mathlib's finitely presented localized-module equivalence theorem |
| D3d input | CartierIdealFinitePresentation | An affine Cartier ideal is finitely presented, proved on principal neighborhoods |
| D3e | CartierIdealStalkNeighborhood | The actual stalk localization and section restriction produce a principal Cartier neighborhood |
| D3d assembly | CartierAffineFppfDescent | Finite affine refinement, affine finite coproduct, faithfully flat descent of finite presentation, then regular stalk spreading |
| D3f | CartierFppfDescent | Global effective Cartier descent along flat surjective locally finitely presented maps |
| D4 | GeneralizedCurveCartierDescent | Fppf-cyclic finite subgroups define relative effective Cartier divisors globally |
| P3a | RelativeAmpleProper | The project's closed-projective-power predicate forces properness |
| P3b | AmpleLineBundle | Standard section-based absolute and relative ample predicates, isomorphism invariance, finite affine section covers, and ampleness of the structure sheaf on affine schemes |

The affine refinement theorem actually only needs a flat surjective **open**
map. Mathlib's `QuasiCompactCover.exists_hom` refines the singleton flat cover
by finitely many affine opens of its source. Their disjoint union is affine,
flat and surjective. The original Cartier condition restricts to each component
and hence to the coproduct. It yields finite presentation upstairs; faithful
flatness descends it. Regular generators descend at stalks using W52. Finally,
finite presentation spreads those generators to principal neighborhoods.

This argument works over arbitrary rings. It does not substitute finite
generation for finite presentation and does not impose Noetherian hypotheses.
The abstract localized basis is converted to an equation in the **actual**
section ring of the basic open, with the given ideal-sheaf restriction.

## Sources and the next proof obligations

- Stacks 01WS and 05B2: Cartier equations and descent of finite locally free
  modules. The proof above now completes the missing D3a–f chain from W52.
- Stacks 01PR, Definition 28.27.1: an invertible sheaf is ample when the scheme
  is quasi-compact and affine nonvanishing opens of positive-power global
  sections cover it. `AmpleLineBundle` records exactly these ingredients, using
  the actual open where the section map from the structure module is invertible.
- Stacks 01VG, Definition 29.38.1: relative ampleness requires a quasi-compact
  morphism and ampleness over each affine target open. This is now expressed by
  `RelativelyAmpleLineBundle`, together with invertibility of the sheaf.
- Stacks 0D2P: fpqc locality of relative ampleness remains unproved.
- Stacks 0B5Y and 0D2S: component degrees and the arbitrary-base fiberwise
  ampleness upgrade remain unproved, as described in the W52 split.

The 01PR and 01VG pages were fetched directly during this wave; untracked
`W53_STACKS_01PR.html` and `W53_STACKS_01VG.html` retain the source text.
The pinned Mathlib has no algebraic-geometric ample-sheaf predicate. The new
standard predicates are explicit definitions, not axioms or projective
presentation assumptions.

The next comparison must retain properness. Our existing `RelativeAmple`
uses **closed** projective presentations and implies `IsProper f`. Ordinary
relative ampleness does not: the structure sheaf of an affine scheme is ample.
The correct comparison target is, for proper `f` and locally free rank-one `L`,

```lean
RelativeAmple f L ↔ RelativelyAmpleLineBundle f L
```

This equivalence is NOT proved here. Its forward direction needs affine
nonvanishing opens for the pulled-back projective coordinates. Its reverse
direction needs sections in a common positive degree and enough sections to
make the associated projective morphism an immersion; properness then closes
that immersion. `AmpleLineBundle.finite_section_cover` supplies finite affine
section opens, but not a common degree or an immersion.

Only after proving the comparison and standard relative locality/base change/
descent can the existing arbitrary affine-coefficient presentation transport
be promoted to general `AmpleSubgroupBaseChange` and `AmpleSubgroupFppfDescent`.
A7–A8 remain unimplemented in this wave; no record carries these conclusions.
