# R11 partial result: constant-filtration target proved

`ThreeAdicPlan.D_etale_three_constant` is proved in
`FLT/GroupScheme/ConstantFiltrationPurity.lean`:

```lean
theorem D_etale_three_constant (H : FF ZInvTwo) (_hD : InCategoryD H)
    (hf : HasFiltration H constantThree) :
    Pure H.points (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ)
```

The proof establishes the stronger statement without the category-D assumption.
`HasFiltration` records integral Hopf maps and exact sequences, including the
faithfully flat quotient and its canonical torsor comparison. It assumes no
étaleness, purity, splitting, or ramification conclusion.

The filtration gives both an étale integral model and a three-group image of
the full geometric point action. Integral specialization proves unramifiedness
at every odd prime. The dyadic three-group inertia theorem kills inertia at
two. The existing everywhere-unramified number-field theorem then makes the
full action trivial.

## Multiplicative results proved

- `muThree` is an actual finite-flat group scheme: its coordinate algebra is
  the group algebra of `ℤ/3ℤ` over `ZInvTwo`.
- `muThree_pure_cyclotomic` proves its full pointwise three-adic cyclotomic
  action. `diagonalizable_pure_cyclotomic` proves the corresponding result
  for every finite diagonalizable model killed by a prime power.
- `FiniteContinuousGaloisModule.characterDual` constructs the finite
  continuous geometric character dual. Its evaluation pairing is equivariant
  and separates points.
- `pure_cyclotomic_of_characterDual_trivial` proves that triviality of this
  full dual gives the actual p-adic cyclotomic scalar action at any finite
  prime-power level. `primePowerModule` supplies the usual scalar action
  through reduction modulo that prime power.

These results do **not** prove `D_multiplicative_three_cyclotomic` for an
arbitrary integral `muThree` filtration. A filtration by multiplicative
simple factors has not been replaced by a diagonalizability hypothesis.

## Exact remaining work

1. Construct the Cartier dual of an arbitrary chosen finite-flat integral
   Hopf algebra over `ZInvTwo`, retaining finiteness, flatness, its Hopf
   structure, and an equivariant identification of its geometric points
   with `H.points.characterDual`.
2. Prove integral exactness under this duality and its effect on a
   `HasFiltration H muThree` filtration. In particular, identify the dual
   of `muThree` with `constantThree`, and obtain an étale dual model and
   a trivial-three filtration of its full point group. Duality reverses
   each short exact sequence; obtaining a filtration in the existing
   constructor order requires refinement or a corresponding closure lemma.
3. Apply the proved constant-filtration arithmetic and character-dual
   cyclotomic theorem. Preserving category D under duality is unnecessary,
   since the constant-filtration theorem does not need that assumption.

The remaining obstacle is integral Cartier duality and filtration transport,
not the roots-of-unity character identity or local/global ramification step.
No action or decision from Kelvin is needed. The brief explicitly permits
shipping the étale case when a sublemma is out of reach; this is a partial
handoff, not a claim that both original targets are complete.

## Verification

Checked at 2026-09-28 01:23 UTC. Each of the 18 new Lean modules was built
individually with `lake build MODULE`. All 52 explicit new theorems are
listed in `/tmp/r11-all-axioms.lean`; all checks pass and only `propext`,
`Classical.choice`, and `Quot.sound` occur in its output. All 18 modules
pass the 15 default linters in `/tmp/r11-final-lint.lean`, including
`docBlame`, `defsWithUnderscore`, and `unusedArguments`.

Recheck the main outputs with:

```sh
lake build FLT.GroupScheme.ConstantFiltrationPurity
lake build FLT.GroupScheme.DiagonalizablePointPurity
lake env lean /tmp/r11-all-axioms.lean
lake env lean /tmp/r11-final-lint.lean
```

`FLT.lean` has 654 imports in ASCII order, exactly matching the 654 Lean
files under `FLT/`. `git diff --check` passes. Only new files and the allowed
imports in `FLT.lean` were changed relative to `720d67f1`; the supplied
untracked `PLAN.ref.md` is unchanged. Commits are on `task/r11`; no push
was performed.
