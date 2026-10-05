# Canonical principal models under coefficient enlargement

This increment addresses the canonical-localization comparison needed by
L1 (Stacks 0D2S). It does not prove L1, glue a family, or remove
`Mazur_statement` from the Fermat endpoint.

## Scalar extension of a fixed model

`integerModelBaseChangeEquiv` identifies `A₁ ⊗[A₀] P.ModelOfHasCoeffs A₀`
with `P.ModelOfHasCoeffs A₁` for an inclusion of coefficient subrings.
Its value on `1 ⊗ b` is `integerModelTransition P h b`.
The construction uses the extension and uniqueness theorems for model maps;
it requires no flatness of the coefficient inclusion.

## Compatible presentations

`integerBaseChangedPresentation` starts from a presentation of `C₀` over
`A₀` and an identification `A ⊗[A₀] C₀ ≃ₐ[A] C`. It gives a presentation
of `C` whose original-stage model identifies with `C₀`. The identification
retains recovery in `C`.

`integerBaseChangedModelEquivAt` identifies every enlarged-stage model of
this presentation with `A₁ ⊗[A₀] C₀`. On transitioned old elements it is
the pure-tensor inclusion.

## Canonical localizations

`integerPrincipalBaseChangeEquiv` identifies `A₁ ⊗[A₀] Localization.Away x`
with `Localization.Away (integerModelTransition P h x)`. Its formula on
localized old elements retains the canonical chart map.

`integerPrincipalPresentationEquiv` combines this with a compatible finite
presentation of the old localization. Thus the enlarged presentation model
is identified with the canonical localization, with an explicit formula
for its inverse on every old localized element.

`exists_integer_model_principal_isomorphism` starts with a map from the old
localization to a fixed target presentation model, recovering the original
principal-localization identification. It produces an equivalence from the
canonical localization of an enlarged source model to the enlarged target
model. The equivalence retains the old comparison on every localized
element. Its inverse is constructed by the eventual-isomorphism theorem;
no inverse at the original coefficient stage is assumed.

`integerPrincipalComparison_recovery` reduces recovery of a localization
comparison to recovery on the source chart. The resulting
`exists_integer_model_principal_chart_isomorphism` retains the full
transported chart map at the enlarged stage. With the supplied
factorization, `exists_integer_model_principal_openImmersion` proves that
the spectrum of that actual transported map is an open immersion.

`exists_integer_model_principal_chart` starts only from a fixed model map
recovering the canonical principal chart and a marked source model element.
It first constructs a localization factorization using eventual units,
then obtains an open immersion at a further coefficient stage. The equality
of recovered marked elements and composition of model transports identify
the final map with the transport of the original fixed map. No factorization
or unit at the initial stage is required.

## Remaining work

- Descend finite principal refinements of general overlaps, including
  overlap pullback identifications and triple-overlap compatibility.
- Descend transition units, glue the family and invertible sheaf, and prove
  the pullback identifications.
- Descend properness and fiber data for the proper-only form of 0D2S;
  do not insert an extra finite-presentation assumption.
- Prove L2 (0D2N), transfer through approximation, then discharge A7–A8.

## Validation contract

The untracked W79 handoff records the checked commit, per-module foreground
build and lint results, declaration axiom audit, and post-merge root build.
To check the present source state, run `python3 W79_CHECK_SOURCE.py` in the
worktree containing that handoff. The handoff supplies its checked-at time
and evidence files; this document describes the theorem contracts.
