# W57: fpqc ampleness descent, source match and first reductions

Source checked 2026-10-04 against Stacks tag
[0D2P](https://stacks.math.columbia.edu/tag/0D2P), including its proof, and
`descent.tex`, label `lemma-descending-property-ample`.
The task's EGA IV 2.7.2 pointer is matched here through the explicit Stacks
statement; no independently checked transcription of EGA is claimed.

## Exact target

The cover is **on the base**: for `f : X ⟶ S`, `g : T ⟶ S` flat, surjective
and quasi-compact, and an invertible sheaf `L` on `X`, deduce ampleness relative
to `f` from relative ampleness of its actual pullback to `X ×[S] T`.
This is not reflection of absolute ampleness along an arbitrary cover of `X`.
No Noetherian, reduced, or finite-presentation assumption on `g` is allowed.
For the project's closed-presentation predicate, the immediate consumer is a
proper `f`; W55 compares its predicate with section ampleness.

The remaining consumer contract is:

```lean
{X S T : Scheme} {f : X ⟶ S} [IsProper f]
{L : X.Modules} (hline : LocallyFreeRankOne L)
(g : T ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]
(hL : RelativeAmple (pullback.snd f g)
  ((Scheme.Modules.pullback (pullback.fst f g)).obj L)) :
RelativeAmple f L
```

This contract is **not implemented** by W57. Properness of the original family
is available in the Mazur consumer. A stronger version deriving properness
from the pullback also needs descent of properness; it is not silently assumed.

## Source proof and dependencies

0D2P forms the graded algebra `A = ⨁ d, f_* (L^⊗d)` on the base. Its graded
pieces are quasi-coherent and commute with flat base change
([02KH](https://stacks.math.columbia.edu/tag/02KH), degree zero).
Faithful flatness reflects surjectivity of the evaluation maps on stalks.
This defines the canonical map to relative Proj
([01O9](https://stacks.math.columbia.edu/tag/01O9)). The map is an open
immersion after the cover by the ample criterion
([01VJ](https://stacks.math.columbia.edu/tag/01VJ)); open immersions descend
([02L3](https://stacks.math.columbia.edu/tag/02L3)). The same criterion then
proves ampleness downstairs.

In the proper case, W56 supplies base-open locality and arbitrary base change,
so one can work over an affine base. W57 further reduces the covering scheme
to an affine one. These reductions preserve actual cartesian squares and
actual module-sheaf pullbacks, not just isomorphism classes of unrelated lines.

## Implemented leaves

Each module has a 240-line cap, including headers. Recheck with
`LEAN_NUM_THREADS=2 lake build MODULE`, then `lake exe runLinter MODULE`, one
module at a time. The untracked handoff carries timestamps, logs and commits.

| Leaf | Module | Proved result |
| --- | --- | --- |
| D0a | `AffineFpqcRefinement` | For affine `S`, refine `g` through an affine `Z`, retaining `k : Z ⟶ T` and flatness/surjectivity of `k ≫ g` |
| D0b | `RelativeAmpleFpqcRefinement` | Refine an actual ample cartesian pullback while retaining the new cartesian square and the actual pulled-back coefficient |
| D1a | `FlatFiniteEqualizer` | Flat scalar extension of a finite-product kernel, with the componentwise pure-tensor formula |
| D1b | `FlatSectionEqualizer` | Flat scalar extension of global sections equals compatible tuples of extended local sections on a finite open cover; unique global tensor and restriction formula |

D0a uses quasi-compactness of the cover itself. It does not replace it with an
openness hypothesis, which would exclude some fpqc maps. The refined composite
is automatically quasi-compact because both schemes are affine.
D1b needs neither quasi-coherence nor separatedness: it is a sheaf equalizer
statement for any finite open cover. Those geometric hypotheses enter when
identifying the local tensors with sections on the scheme base change.

## Next capped leaves, in dependency order

These are proof obligations, not completed results or assumed structure fields.
Each proposed module must stay at most 240 lines; subdivide further where needed.

| Leaf | Proposed module | Exact missing bridge | Dependencies |
| --- | --- | --- | --- |
| D2a | `AffineModulePullbackSections` | For a map of affine schemes and quasi-coherent `M`, identify `Γ(Y,O) ⊗[Γ(X,O)] Γ(X,M)` with `Γ(Y,p* M)` via the actual adjunction-unit section map | Tilde/pullback compatibility |
| D2b | `AffineCartesianSectionScalars` | In an affine cartesian square, identify that coefficient extension with `B ⊗[A] Γ(U,M)`; retain pure-tensor formula | D2a, affine pullback ring comparison |
| D2c | `FlatPullbackSectionRestriction` | Show these identifications commute with restriction to chart intersections | D2a–b |
| D2d | `FlatGlobalSectionBaseChange` | For separated quasi-compact `X` over affine `Spec A` and flat `A → B`, prove `B ⊗[A] Γ(X,M) ≃ Γ(X_B,p* M)` with the actual section map | D1b, D2b–c, finite affine cover |
| D3a | `LinePowerEvaluationBaseChange` | Identify pullback of the evaluation of global degree-`d` sections with evaluation upstairs | D2d, tensor-power pullback coherence |
| D3b | `LinePowerEvaluationDescent` | Reflect stalk surjectivity in some positive degree using faithful flatness of the local stalk map | D3a, actual sheaf-stalk pullback comparison |
| D4a | `SectionAlgebraProjMap` | Build the canonical map to Proj of the full graded section algebra from the descended evaluation maps | D3b, graded algebra/Proj construction |
| D4b | `SectionAlgebraProjBaseChange` | Identify its actual flat base change with the canonical map upstairs | D4a, D2d |
| D4c | `AmpleSectionAlgebraCriterion` | Prove the section-ampleness/open-immersion criterion of 01VJ | D4a, affine Proj chart theory |
| D4d | `SectionAlgebraImmersionDescent` | Descend the open immersion and obtain section ampleness | D4b–c, 02L3 |
| D5 | `RelativeAmpleFpqcDescent` | Assemble affine refinement, affine descent, base locality, and the proper closed-presentation comparison | D0b, D4d, W55–W56 |

The first absent geometric identification is D2a. `ModulePresheafPullbackSections`
computes **presheaf** pullback by a filtered colimit; it is not already the
quasi-coherent **sheaf** affine comparison. Likewise `SectionBaseLocalization`
handles localization at a principal base element, not an arbitrary flat algebra.
Neither should be substituted for D2a–d without the additional proofs.
D1b alone does not prove flat base change of scheme cohomology or ampleness.

The Proj leaves are substantial: existing finite projective-space presentation
modules do not by themselves construct the map for the full graded section
algebra. Their 240-line entries are interface caps, not estimates of total work.

## Subsequent goal boundary

After D5, complete the component degree/support and ample-degree results and the
arbitrary-base fibre-to-neighborhood theorem of 0D2S (F1–F3, L1–L2 in
`MAZUR_W52_SPLIT.md`). Then implement A7–A8. W57 does not establish any of these
results and does not remove `Mazur_statement` from the endpoint theorem.
