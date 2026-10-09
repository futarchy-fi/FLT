# G1-C: coarse modular curve foundation split

Audit checked 2026-10-09 against this checkout's mathlib and the live Stacks sources.
The application contracts are C1--C8 in `MAZUR_CONTRACTS.md`.
No coarse modular curve is constructed by the A7/A8 ampleness results.

## Source correction and scope

The two proposed tags do not supply the required general quotient theorem:

- [07S7](https://stacks.math.columbia.edu/tag/07S7), Lemma 66.14.2, assumes a
  **free** action by a finite locally free group scheme. Its conclusion is an
  fppf quotient scheme and a torsor. It cannot remove nontrivial stabilizers.
- [07S9](https://stacks.math.columbia.edu/tag/07S9), Lemma 68.8.4, is about
  stratification of a reasonable algebraic space by schemes, not finite-group
  quotients of quasi-projective schemes.

For the affine foundation use Stacks, *Groupoids in Algebraic Geometry*,
section "Finite flat groupoids, affine case". The exact source labels in
[`groupoids.tex`](https://github.com/stacks/stacks-project/blob/master/groupoids.tex)
are `equation-invariants`, `lemma-determinant-trick`,
`lemma-integral-over-invariants`, `lemma-invariants-base-change`, and `lemma-points`.
Their finite constant-group specializations suffice for the first leaves below.
Do not invoke `proposition-finite-flat-equivalence` for a group action with
stabilizers: that proposition assumes the relation morphism is a monomorphism.

Two routes were considered: the free-action torsor theorem, and gluing spectra
of invariant rings on invariant affine opens. Use the latter, since it allows
stabilizers. A full nonfree scheme quotient and its universal property remain
foundation theorems to prove, not fields to request in an atlas record.

## Existing ingredients, checked in source

- `Mathlib.RingTheory.Invariant.Basic`: integral extension over invariants and
  transitivity of the finite group on primes over a prime.
- `FixedPoints.subring`: the actual fixed subring, with its injective inclusion.
- `PrimeSpectrum`: lying over, closedness of integral maps, principal-open topology.
- `VeryAmpleAffineSections`: an actual closed projective presentation supplies
  affine generator opens; `RelativeVeryAmpleLineBundle` retains the embedding
  and its hyperplane sheaf comparison.
- `DivisorPowerVeryAmple`: transports divisor powers to their actual tensor powers.
  It does not construct a presentation from a quotient hypothesis.
- A7/A8: actual ample cyclic classes and rational torsion classes, with pullback.
  No atlas representability or invariant affine orbit neighborhood follows merely
  by renaming these presheaves.

Reproduce the foundation inventory by reading those modules and searching
`Mathlib/AlgebraicGeometry` for quotient/group-action constructions. The only
scheme quotient needed here was not found in that search.

## Ordered foundation leaves (each implementation module at most 240 lines)

| Leaf | Concrete result | Input/source |
| --- | --- | --- |
| FQ1 | Fixed subring; invariant ring-map factorization | equation-invariants |
| FQ2 | Integral inclusion, closed surjection, prime orbits | integrality; points |
| FQ3 | Fixed-ring spectrum; affine universal property | FQ1; Spec adjunction |
| FQ4 | Finite and proper quotient map for finite-type algebras | FQ2; integral + finite type |
| FQ5 | Invariant principal localization comparison | invariants-base-change |
| FQ6 | Algebraically closed field points are exactly group orbits | lemma-points, part (2) |
| FQ7 | Invariant affine neighborhoods of finite orbits | actual ample/very-ample sections |
| FQ8 | Glue affine quotients and their structure maps on overlaps | FQ5, FQ7 |
| FQ9 | Universal property for arbitrary scheme targets; flat base change | FQ3, FQ5, FQ8 |

FQ2 only concerns underlying primes: it must not be presented as FQ6's theorem
about field-valued morphisms. FQ4 proves properness of the quotient map, not C5
properness of the modular curve over its arithmetic base. Invariants commute
with flat base change; arbitrary base change requires the weaker statements
in `lemma-invariants-base-change`, not an unjustified ring isomorphism.

## Application queue after the foundation

C1 constructs the rigidified generalized-elliptic level atlas, including its
representability and actual finite-group action. C2 applies FQ8/FQ9 and descends
c. C3 proves the contract's `CoarseUniversal`, and C4 uses geometric orbit
classification including the boundary. C5--C7 separately prove properness,
smooth relative dimension one (including characteristic 3), and geometric
integrality. C8 sends the existing prime torsion moduli class through c and
proves both cusp inequalities. Exceptional automorphism and boundary charts
must be checked; freeness and smoothness cannot be assumed in record fields.

The atlas/quotient foundation is not charged to the C1/C2 application budget.
Track D's local arithmetic and G2's Picard/Jacobian constructions stay with their
existing workers. The interrupted Picard/arithmetic files in this worktree are
outside this split and must not be silently counted as G1-C progress.

## Implemented affine foundation and remaining gate

Checked 2026-10-09: FQ1--FQ6's affine results are implemented in the new
`FiniteGroup*` and `InvariantLocalization*` modules. In particular:

- `FiniteGroupAffineQuotient.existsUnique_affine_desc` constructs descent to
  spectra; it does not yet prove the universal property for arbitrary schemes.
- `FiniteGroupQuotientPrincipalChart.principalQuotientOpenIso` identifies actual
  principal quotient opens, with the coordinate-map and structure-map comparisons.
- `FiniteGroupInvariantOpens.exists_invariant_basicOpen` constructs invariant
  principal neighborhoods inside invariant opens of an **already affine** scheme.
- `FiniteGroupQuotientGeometricPoints.fieldPointMap_bijective` and
  `FiniteGroupQuotientSchemePoints` classify actual algebraically closed points.
  This includes stabilizers and arbitrary characteristic for affine actions.

These names are module-qualified here; the declarations share the namespace
`FLT.Mazur.FiniteGroupQuotient`. Each module is at most 240 lines and was built,
linted individually, and audited for only the three standard axioms. Validation
logs and the reproducible manifest remain outside the tracked source directories.

## Non-affine neighborhoods and overlap foundations implemented in W174

Checked 2026-10-09 against the named declarations below. Each new module has a
bounded foreground probe, module build, individual lint, and declaration axiom
audit; the reproducible `W174_RECHECK.py` and manifest accompany the local handoff.
All these modules remain at most 240 lines.

- `HomogeneousIdealWitness` extracts positive homogeneous components outside a
  homogeneous ideal. `HomogeneousPrimeAvoidance.exists_positive_avoiding` proves
  Stacks [00JS](https://stacks.math.columbia.edu/tag/00JS), including finite residue
  fields and nontrivial containments among the primes.
- `ProjectiveFiniteAffineNeighborhood.exists_basicOpen` puts every finite set in
  an open of Proj inside one positive homogeneous basic open contained in it.
- `AmpleFiniteAffineNeighborhood.of_ample` transfers this through the established
  section-ring Proj open immersion, proving the required
  [01ZY](https://stacks.math.columbia.edu/tag/01ZY) neighborhood result.
- `FiniteGroupAffineNeighborhood.exists_invariant_affine` intersects translates
  and proves that the orbit remains in an affine invariant neighborhood.
  `FiniteGroupInvariantAffineCover` assembles the actual cover and affine overlaps.
  These results assume a separated scheme with the existing ample line bundle.
- `FiniteGroupOpenRestriction` constructs the genuine restricted actions and
  proves equivariance of inclusions between stable opens.
- `SchemeCoordinateAction` constructs inverse-pullback actions on global sections.
  `SchemeFiniteGroupQuotient` applies the fixed-ring quotient to actual affine
  schemes, with invariant, integral, surjective quotient maps.
- `SchemeFiniteGroupQuotientMaps` constructs maps of fixed rings and quotient
  spectra, retaining naturality and composition. The composition law alone does
  not constitute a glued scheme or full gluing data.
- `SchemeFiniteGroupQuotientOrbits` proves that the fibers are the original
  scheme-action orbits and that stable opens descend to opens.
- `SchemeFiniteGroupQuotientOpenEmbedding` proves the induced map of quotients
  of an equivariant affine open immersion is a **topological** open embedding.
  This theorem alone does not establish its structure-sheaf isomorphisms.
- `SchemeFiniteGroupPrincipalQuotient` proves a **scheme** open immersion for an
  invariant principal-open inclusion using the fixed-ring localization theorem.
- `SchemeFiniteGroupInvariantPrincipal` gives invariant principal neighborhoods
  inside stable opens and identifies the actual principal quotient image.

Module names above are under `FLT/Mazur/`; namespaces are documented in source.
FQ7 is now proved. The D and G2 lanes remain outside this work.

## Global quotient and affine-target descent implemented in W175

Checked 2026-10-09 against the declarations below. Reproduce the source hashes,
line caps, bounded probe logs, foreground builds, individual lints, declaration
axiom audits, main ancestry, and root build with `python3 W175_RECHECK.py` in
this worktree. The local handoff and manifest stay outside tracked source paths.

- `SchemeFiniteGroupQuotientIso.quotientIso` constructs the quotient isomorphism
  of an actual equivariant scheme isomorphism, including its inverse.
- `SchemeFiniteGroupPrincipalComparison.principalChartIso` identifies inverse-image
  principal charts inside the image of an open immersion. The comparison is
  equivariant and its quotient commutes with the ambient quotient maps.
- `SchemeFiniteGroupQuotientOpenImmersion.quotientHom_isOpenImmersion` proves the
  general scheme-level overlap assertion by a cover of invariant principal opens.
- `StableAffineQuotientDiagram` constructs the diagram of all actual invariant
  affine opens and their invariant-coordinate quotients. Its arrows are open immersions.
- `StableAffineQuotientOverlap.diagram_isLocallyDirected` proves the overlap
  condition using actual orbit fibers and affine intersections on a separated scheme.
- `StableAffineQuotientGluing.glueData` applies scheme gluing to that proved diagram;
  `glueData_cocycle` is the full scheme pullback cocycle. `glued`, `chartMap`, and
  `gluedCover` give the actual quotient scheme, chart maps, and open cover.
- `StableAffineQuotientMap.map` glues the original quotient maps to an invariant
  surjective global morphism. `AmpleFiniteGroupQuotient.ample_charts_cover` supplies
  coverage from the established ample line bundle, and `ampleMap` applies it.
- `StableAffineQuotientChartPreimage.map_preimage_chart` identifies every original
  affine chart as the inverse image of its quotient chart.
- `StableAffineQuotientCartesian.chart_isPullback` proves the chart squares are
  cartesian. `map_integral`, `map_isQuotientMap`, and `map_eq_iff_orbit` prove
  integrality, the quotient topology, and exact orbit fibers of the global map.
- `SchemeFiniteGroupAffineDescent.existsUnique_affine_desc` transports coordinate
  descent to actual affine source and target schemes.
- `StableAffineQuotientAffineDescent.existsUnique_affineDesc` constructs unique
  descent from the glued quotient to any affine target, using an actual cocone
  of the unique local descents. This does not yet handle arbitrary scheme targets.

These are module-qualified descriptions; the source specifies the shared namespaces.
FQ8's overlap and scheme gluing construction is now proved for separated schemes
with the established ample line bundle. FQ9 remains open beyond affine targets.

## Next missing proof and ordered remaining work

1. Extend the quotient universal property to arbitrary scheme targets (FQ9).
   Cover the target by affine opens and use stable inverse images and invariant
   principal neighborhoods in affine source charts. Construct the local descents,
   prove their agreement as scheme morphisms, and glue them. The global affine-target
   theorem does not alone provide uniqueness for maps to arbitrary schemes.
2. Prove flat base change for the global quotient, using fixed-ring base change,
   the constructed chart squares, and scheme-level comparison maps (FQ9).
3. Construct the actual rigidified auxiliary level atlas and relation, then C2.
   Prove C3--C8, including boundary points, characteristic 3, geometric integrality,
   and the actual prime-torsion and cusp comparisons. D and G2 stay with their workers.

The source still declares `Mazur_statement` in `FLT/Assumptions/Mazur.lean` and
uses it in `FLT/MazurW.lean`; reproduce with `git grep -n Mazur_statement -- FLT`.
No replacement of that assumption or coarse modular curve is claimed.
