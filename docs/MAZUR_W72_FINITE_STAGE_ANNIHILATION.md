# Finite-stage annihilation and positive-degree ideal-twist vanishing

The W71 finite-stage obligation is proved by
`LineSectionTwistSystem.exists_moduleH_annihilator`. Its inputs are a
compact separated locally Noetherian scheme, a coherent coefficient module
`M`, a line sheaf `L`, and a section `s` with affine generator open. For every
positive cohomological degree, every stage `n`, and every actual module
cohomology class at that stage, it produces `m ≥ n` whose actual
section-twist transition kills the class.

The theorem does not assume a colimit comparison, cohomological
annihilation, or ampleness. The field-linear formulation is
`exists_cohomology_annihilator`.

## Proof components

- `AffineOpenCechBoundary`: the restriction adjunction maps coefficients to
  the direct image of their restriction to an affine open. Affine
  direct-image comparison and affine vanishing supply actual bounding
  cochains on the original affine cover. No equality between two separate
  Ext restriction constructions is needed.
- `LineSectionTwistCoordinates`: under a trivialization, the actual
  transition from stage `n` to `n+d` is multiplication by the `d`-th power
  of the section coordinate.
- `TrivialLineTwistLocalization`: scalar localization proves both
  finite-stage lifting and finite-stage annihilation of sections.
- `LineSectionTwistRestriction`: a natural isomorphism identifies the
  restricted ambient system with the system of the restricted section.
- `LocalLineTwistLocalization` and `AffineLineTwistLocalization`: transport
  the local conclusions to the actual ambient chart and intersection
  section maps used in the direct-image complex.
- `FiniteAffineLineCover`: compactness supplies a finite affine
  trivializing cover; all its tuple intersections retain trivializations.
- `SequentialFiniteProducts`: finitely many lifts or kernel elements admit
  one common stage, by transporting to the maximum of their stages.
- `SequentialCochainBoundary`: lift a bounding cochain, then kill the
  remaining discrepancy at another stage. The conclusion is also proved
  for actual categorical homology, using cycles and the homology quotient.
- `SequentialCechLocalization`: applies that argument to the actual finite
  Cech complex using its natural section coordinates.
- `LineSectionCohomologyAnnihilation`: supplies every local hypothesis from
  the geometric lemmas, then uses coefficient naturality of the
  affine-cover comparison to obtain actual module cohomology annihilation.

## Consequences for a proper integral curve

`idealCohomology_annihilator` specializes the result to the existing system
`idealCohomology f s I (q+1)`, including noninvertible ideal sheaves.
`idealCohomology_eventually_subsingleton` combines it with W71 stabilization:
for a nonzero section with affine generator open, all sufficiently late
stages have zero positive cohomology.

`exists_positive_ideal_power_cohomology_vanishing` combines W70's nonzero
affine section of a positive line power with this vanishing theorem.
Tensor-power reassociation returns to the original line: for every ideal
sheaf `I` and every `q`, there exists `m > 0` such that
`H^(q+1)(X, idealModule I ⊗ tensorPower L m)` is zero when `deg L > 0`.
In particular, this supplies the H¹ hypothesis used at the end of Stacks
0B5X's positive-degree implication.

## Remaining obligation

The cohomological criterion of Stacks 30.17.1, converting this ideal-sheaf
H¹ vanishing into `AmpleLineBundle L`, is not proved here. The existing
ampleness definition requires an affine positive-power section-open
neighborhood at every point. Vanishing alone is not that cover.

Stacks 0B5P (30.3.3) gives the next concrete construction. For a closed point
`x` in an affine trivializing neighborhood `U`, take the reduced ideals
`I` of `X \ U` and `I'` of `(X \ U) ∪ {x}`. Identify the sections of
`(I/I') ⊗ L^m` with the residue field at `x`. H¹ vanishing for `I' ⊗ L^m`
then lifts its element `1` to a section of `I ⊗ L^m`. One must prove that
this lift generates at `x`. `idealTensor_section_generatorOpen_le` and
`isAffineOpen_sectionGeneratorOpen_of_le` provide the support bound and
affineness once that lift is constructed. Finally compactness shows an open
containing every closed point covers the scheme. The quotient identification,
generator-at-the-point proof, and cover assembly are not supplied here.

After this criterion, the ordered remaining work is finite-surjective
ampleness descent (0B5V), the component criterion (0B5Y), F3 on smooth and
polygon fibres, arbitrary-base L1–L2, and A7–A8. This development does not
remove `Mazur_statement` from the Fermat endpoint.

## Reproducible verification

Build each listed module separately with `LEAN_NUM_THREADS=2 lake build
MODULE`; lint each separately with `LEAN_NUM_THREADS=2 lake exe runLinter
MODULE`. The untracked `W72_MODULES.txt`, `W72_VALIDATE.py`, and
`W72_AXIOM_AUDIT.lean` enumerate the modules and check every originating
declaration, including generated ones, against only `propext`,
`Classical.choice`, and `Quot.sound`. `W72_CHECK_SOURCE.py` rechecks source
hashes, line caps, results, commit ownership, and the final merge/root build.
