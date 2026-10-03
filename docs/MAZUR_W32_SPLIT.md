# W32: independent marked sections and projective-line H0

Each leaf was prototyped with Lean before promotion; whole-file cap 240.
Validation commands run in the foreground with LEAN_NUM_THREADS=2, and each
new module is linted individually. The originating-declaration audit permits
only propext, Classical.choice and Quot.sound.

| Item | Module | Proof design |
|---|---|---|
| D05a.3b.1 | ModuleSectionRegularity | Remove the top restriction from a trivialization, cancel regular scalars, and transport local rank-one coordinate relations to a common pullback. |
| D05a.3b.2 | ProjectiveLineMarkedSectionOverlap | Trivialize the Laurent module, compare canonical and independent coordinates, and cancel the regular right equation. Apply to each bounded polynomial and its reciprocal. |
| D05a.3c.1 | ModuleImageSection | Use restriction/pullback composition coherence to translate common-pullback equality into equality of sheaf restrictions on image intersections. |
| D05a.3c.2 | ModuleBinarySectionGluing | Apply the actual additive sheaf condition to two image opens; recover the prescribed module pullbacks. |
| D05a.3c.3 | ProjectiveLineChartIntersection | Transport the standard Proj cartesian square to the original projective line and identify the entire overlap image. |
| D05a.3c.4 | ProjectiveLineMarkedSectionGluing | Glue independently constructed sections, make a structure-module morphism, and prove the existing boundedPolynomial map surjective and bijective. |
| D05a.4a | ProjectiveLineMarkedHZero | Use actual ModuleScalarH in degree zero; prove scalar compatibility through the specified base map and package the polynomial map as a linear equivalence. |

The overlap constructions use named `pullOverlap` and `pullOverlapAlong`
definitions. Their bodies are the pullback-composition and equality-transport
maps of W31's untracked gluing contract. Naming those operations avoids a
large kernel reduction during the converse proof. The result does not assume
that the independent local sections were already global.

The exported global-section surjectivity theorem concerns the existing
`ProjectiveLineMarkedSectionInjective.boundedPolynomial` without changing it.
The H0 equivalence concerns genuine sheaf cohomology and its original scalar
action, rather than a new section-space model.

The remaining D05a.4 endpoint comparison must identify intrinsic node fibers,
not only polynomial evaluations. D04c.2 still needs the existing polygon
power comparison to preserve the powered canonical section, and to identify
the two branch values in the same node fiber with predecessor-oriented
weights. D05b/c requires the tensorized normalization sequence and its maps.
Generation, projective ratio maps, O(1) pullback and closed immersion in
D06-D10 remain, including self-incidence for the one-gon and both two-gon nodes.
No change to Mazur_statement or the final Fermat theorem is asserted here.
