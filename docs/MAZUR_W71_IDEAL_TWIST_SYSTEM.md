# Ideal-twist cohomology in the positive-degree criterion

This development constructs the transition system in the proof of Stacks
0B5X. It does not establish finite-stage annihilation or ampleness.

## Coefficients and maps

For a module sheaf `M`, a line sheaf `L`, and a section `s : Γ(L, ⊤)`,
`LineSectionTwistSystem.system M s` is a functor from the ordered natural
numbers to module sheaves. Its term at `n` is the actual sheafified tensor
`M ⊗ tensorPower L n`. Its successor map inserts `s` into the line factor.
`powerStep_app` and `step_pure` identify this map on local sections.

This construction accepts a section of a positive power of another line:
take `L := tensorPower L₀ d`. The existing `tensorPowerMulIso` identifies
the resulting powers with `tensorPower L₀ (d * n)`.

The restriction of every successor map to `sectionGeneratorOpen L s` is an
isomorphism. This follows from the actual restricted section morphism and
naturality of tensor restriction in both tensor factors.

## Cohomology and geometry

`cohomology f M s q` applies `moduleScalarHFunctor f q` to that system.
`openCohomology` first restricts its coefficients to an open subscheme.
`restriction` is a natural transformation between these systems over the
same base field. Its naturality is proved for arbitrary coefficient maps.
For coherent coefficients and an affine open, it is zero in positive degree.
`idealCohomology f s I q` specializes to `M := idealModule I`.

On a reduced scheme, a section of a line with empty generator open is zero.
Consequently a nonzero section on an integral scheme generates at the generic
point. On an integral Noetherian curve, every coherent twist successor map
therefore has finite-support cokernel.

The generic stalk detects zero morphisms into a line sheaf. Hence a source
embedded in a line has the property that generic injectivity of a map implies
global injectivity. Applying this to the canonical inclusion of the ideal
twist into the line power proves `idealStep_mono`; no invertibility hypothesis
on the ideal is used.

For a proper integral curve over a field with topological dimension at most
one, `idealStep_cohomology_surjective` proves surjectivity in every positive
cohomological degree. The proof uses the cokernel short exact sequence and
vanishing of positive cohomology for coherent finite-support sheaves.

Proper coherent finiteness then proves `idealCohomology_eventually_isIso`:
there is a stage from which every later map is an isomorphism. The proof
chooses a term of minimum finite dimension and uses surjectivity.

## Remaining mathematical obligation

The stable cohomology need not vanish merely because its restriction to an
affine open is zero. The missing geometric assertion, in the notation above,
is: for each `a : (idealCohomology f s I 1).obj n`, there exist `m ≥ n` such
that `(idealCohomology f s I 1).map (homOfLE h) a = 0`, provided the generator
open of `s` is affine. This is the finite-stage statement used in Stacks
30.17.4. It is not a hypothesis of any geometric vanishing theorem added here.

A route to this assertion is to represent the class on a finite affine
trivializing cover, restrict its cocycle to the affine generator open, lift a
bounding cochain after multiplying by a common power of the section, and
kill the remaining overlap discrepancies by a further common power. The
comparison with actual Ext-based cohomology must commute with these maps.
The existing `affineCoverCechEquiv_naturality` supplies coefficient naturality;
the necessary comparison with restriction to the generator open and the
arbitrary-line cochain denominator argument remain to be constructed.

After finite-stage annihilation, the stable-stage isomorphisms imply zero
cohomology in sufficiently high stages. One must still prove the
cohomological criterion that produces an affine-section-open cover, then
finite-surjective ampleness descent (0B5V), the component criterion (0B5Y),
F3, L1–L2, and A7–A8. These statements are not established by this development.

## Verification

Build each of the five new modules separately with `LEAN_NUM_THREADS=2 lake
build MODULE`. Run `lake exe runLinter MODULE` separately for each module.
The untracked `W71_AXIOM_AUDIT.lean` checks every originating declaration,
including generated declarations, against `propext`, `Classical.choice`,
and `Quot.sound`. The root `lake build FLT` checks import compatibility after
merging main. These are reproducible checks, not claims that the remaining
Mazur endpoint has been discharged.
