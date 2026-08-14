# Mazur W statement draft

## API choices

- The file follows `FLT/Assumptions/Mazur.lean`: Mathlib affine elliptic
  points, `open scoped WeierstrassCurve.Affine`, and an
  `[E.IsElliptic]` typeclass binder.
- `mazur_W` uses an injective additive homomorphism
  `((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point`.  The outer parentheses make
  the intended `(Z/2)^2 × Z/ℓ` bracketing explicit; this avoids any dependence
  on the associativity of `×` notation.  Injectivity says exactly that the
  rational-point group contains a copy of the domain, without constructing a
  separate subgroup object.
- `mazur_W` is parameterized by `E` with `[E.IsElliptic]`.  Its universal
  theorem arguments are the clean typeclass-friendly form of the frozen
  assertion that no such elliptic curve exists.
- `mazur_W_ge11` uses `¬ ∃ P, addOrderOf P = ℓ` for nonexistence of a rational
  point of exact prime order.  The declaration contains no torsion-set
  cardinality API.
- The two definition tests use the same injection API: a requested positive
  `ZMod 2 × ZMod 10` fixture and a full-2-torsion non-vacuity fixture.

## Elaboration risks

- The elliptic-point group instance needs both `E.IsElliptic` and the affine
  point scope; removing either can make the `AddMonoidHom` codomain fail to
  elaborate.
- In the existential definition tests, the ellipticity witness is installed
  with a local `letI`; an instance binder cannot be placed directly after an
  existential binder.
- Keep `ℓ` as `ℕ` with an explicit `ℓ.Prime` hypothesis.  Introducing a
  `Fact ℓ.Prime` binder would make the panel-facing quantifiers less explicit.
- `addOrderOf` is the additive-group API; `orderOf` is the multiplicative
  analogue and is the wrong declaration here.
- The file elaborates with `lake env lean` from `/Users/kas/FLT` against the
  checked-in dependency snapshot.  The check writes nothing to the read-only
  checkout and currently reports only the four expected `sorry` warnings.

## Panel re-check items

- `mazur_W_ge11` is not a formal corollary of the frozen `mazur_W` statement:
  W only excludes an `ℓ`-point when the same curve also has full rational
  `2`-torsion.  The no-point declaration is a stronger Mazur-classification
  projection and needs its own proof route or stronger upstream theorem.
- Confirm the exact threshold interface: the reconciled map places the hard
  modular core at `ℓ ≥ 17`, while this draft exposes the requested stronger
  `ℓ ≥ 11` statement for the eventual small-prime plus D8/D9 assembly.
- Re-check the requested positive `Z/2 × Z/10` sanity declaration.  By the
  Chinese-remainder decomposition it has the same abstract 2-primary/5-part
  shape as `(Z/2)^2 × Z/5`, so a proof of literal Mazur W at `ℓ = 5` would
  contradict that positive fixture.  It is also absent from Mazur's actual
  torsion classification.  Keep it as the requested sorry-bodied trap, but
  do not admit both declarations as proved without a panel scope change.
- For A5, verify the missing ch03 bridge (character reducibility, rational
  point extraction, quotient and A4 survival) before replacing
  `knownin1980s`; coordinate PQ7 when retiring `Mazur_statement`.
