# W78: comparison maps under coefficient enlargement

This increment proves finite-stage comparison results needed by L1 /
Stacks 0D2S. It does not yet descend a general overlap open immersion or
construct a glued family. L2 / 0D2N and A7–A8 remain unfinished.

## Contracts

All declarations below are in `FLT.Mazur.Approximation`.

| Module | Result |
| --- | --- |
| `IntegerModelHomExtension` | A scalar-compatible map from an old presentation model extends uniquely to an algebra map from its enlargement. |
| `IntegerModelHomTransport` | Transport maps between fixed models, preserve their recovery, and compose coefficient transitions. |
| `CommonModelEventualEquality` | Finite vanishing data and pairs of maps into finitely many fixed models become equal at a common stage. |
| `IntegerModelEventualInverse` | Model maps recovering inverse identities become an algebra equivalence after enlargement. |
| `IntegerModelIsomorphismDescent` | A fixed model map recovering an isomorphism becomes an isomorphism; its inverse is constructed from the original inverse. |
| `IntegerModelEventualUnits` | Finitely many fixed model elements recovering units become units with exactly their transitioned values. |
| `PrincipalComparisonIntegerModel` | A fixed map factors through a principal localization after its marked image becomes a unit. |

Each new module is capped at 240 lines. Existing Lean modules are changed
only by adding sorted imports to `FLT.lean`.

## Extending and transporting maps

`integerModelExtendHom` evaluates the new polynomial presentation at the
images of the old generators. The scalar compatibility hypothesis proves
that evaluation after coefficient inclusion agrees with the old map.
The old relations therefore imply the new relations.

`integerModel_hom_ext` proves uniqueness: an algebra map from the enlarged
model is determined by its values on the transitioned old model. This
uses the old polynomial generators, not surjectivity of the transition.
`integerModelTransportHom` applies this extension to a model map followed
by the target transition. Its recovery theorem retains the given original
algebra map on every element of the enlarged model.

## Actual inverse comparisons

`exists_integer_model_eventual_inverse` starts with two algebra maps at
one stage and equations asserting that their composites recover the
identities. It equalizes the first composite, transports both maps, then
equalizes the second composite. The first equality survives the second
enlargement. Extensionality from the old generators establishes both
identities on the entire final models and constructs an `AlgEquiv`.

`exists_integer_model_isomorphism` requires only a model map and an
original algebra equivalence that it recovers. It lifts the original
inverse with scalar compatibility, extends it to the enlarged model,
then applies eventual inverse comparison. The resulting equivalence both
extends the old model map and recovers the original equivalence.
No inverse at the initial coefficient stage is assumed.

The separate simultaneous equality theorem handles finite families of
models and equations, for later finite gluing applications. Neither
argument assumes that quotient transition maps are injective or that
scalar extension from an integer subalgebra is faithfully flat.

## Principal comparisons

`exists_integer_model_eventual_units` descends inverse polynomials and
the equations saying their products with the old marked elements are
one. The units' values are the old elements under `integerModelTransition`.
This preserves the particular map being compared.

`exists_integer_model_principal_comparison` applies this result to the
image of a marked source element. The transported map then factors
through the canonical localization of the enlarged source model. Its
factorization identity holds at that coefficient stage, not merely after
recovery. The localization chart is an open immersion by W77's
`principalIntegerModel_isOpenImmersion`.

This does **not** prove that the comparison out of the localization is an
isomorphism, or that the original descended overlap arrow is an open
immersion. The isomorphism theorem above concerns fixed presentation
models; connecting those models to canonical localized source models is
still required.

## Remaining work, in order

1. Identify canonical localizations of enlarged models with compatible
   presentation models. Construct both principal comparison maps, prove
   recovery, and enforce their inverse equations at a common stage using
   the new extension and eventual-inverse APIs.
2. Descend general overlap open immersions using finite principal
   refinements. Retain overlap pullback identifications and triple-overlap
   compatibility while assembling finite affine gluing data.
3. Descend transition units compatibly with all overlap maps, glue the
   family and invertible sheaf, and identify their pullbacks.
4. Descend properness and fiber data and an ample fiber presentation. The
   proper-only form of 0D2S still needs inverse-system approximation; an
   additional finite-presentation assumption does not replace it.
5. Prove the Noetherian ample-neighborhood result L2 / 0D2N and transfer
   it through approximation. Then finish A7–A8.

## Validation

Run each new module's foreground build with `LEAN_NUM_THREADS=2`, then
`lake exe runLinter MODULE` sequentially. Audit every originating
declaration against `propext`, `Classical.choice`, and `Quot.sound`.
After merging `origin/main`, build `FLT` once for coexistence checks.
The untracked `MAZUR_W78_DONE.md` records the checkpoint, actual validation
results, local commit, and remaining work. `python3 W78_CHECK_SOURCE.py`
rechecks the source hashes, scope, line caps, logs, and merge ancestry.
