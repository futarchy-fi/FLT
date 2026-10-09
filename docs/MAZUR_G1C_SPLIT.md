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

The next missing theorem is [01ZY](https://stacks.math.columbia.edu/tag/01ZY),
Lemma 28.30.5: every finite set in a scheme with an ample invertible sheaf lies
in a common affine open. `VeryAmpleAffineSections` supplies individual affine
neighborhoods, not one affine neighborhood of a whole orbit. The required bridge
is not obtained by intersecting an arbitrary affine cover of the points.

Split FQ7 further before the global gluing step:

1. Homogeneous prime avoidance, Stacks [00JS](https://stacks.math.columbia.edu/tag/00JS),
   Lemma 10.57.6, for finitely many homogeneous primes and a homogeneous ideal.
2. Use it to prove 01ZY for locally closed subschemes of Proj, retaining an actual
   affine basic open that contains the whole finite set and avoids the boundary.
3. Reuse `SectionGradedProjOfAmple.isOpenImmersion` to transfer this to schemes
   with the existing ample line-bundle predicate.
4. For a finite group action, intersect the translates of the common affine
   neighborhood to obtain a stable affine neighborhood; prove affineness using
   separatedness and prove that it still contains the orbit.

FQ8 must then construct the action on each affine chart's coordinate ring,
compare restrictions on invariant principal overlaps, prove the cocycle, and
apply scheme gluing. FQ9 extends descent to arbitrary scheme targets and proves
flat base change. None of those global theorems, or C1--C8, is claimed here.
The specified tags 07S7/07S9 cannot discharge these gaps.
