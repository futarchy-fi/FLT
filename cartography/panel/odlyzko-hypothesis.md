# Odlyzko chapter — adversarial panel note (Hypothesis Strength + Triviality)

Seat: adversarial panel, FLT-on-Lean campaign. Target: `hub-lsb1u.6.12`,
reviewing `cartography/odlyzko-reconciled:cartography/odlyzko-reconciled.md`
against repo ground truth (`FLT/Assumptions/Odlyzko.lean`,
`FLT/GaloisRepresentation/HardlyRamified/*.lean`, blueprint chapters 3–4).
Default posture: skeptical. Scope: sufficiency and vacuity only.

## Verdict

**NOT independently verifiable as sufficient from repo ground truth, and the
reconciled map's flagship numerical argument for sufficiency is unsourced.**
The axiom's hypothesis shape (totally complex, `finrank ≥ 18`) is architecturally
plausible and not vacuous, but nothing in the repo currently states or proves
the matching discriminant *upper* bound the Fontaine-style consumer argument
needs, so "8.25 suffices" cannot be checked against this codebase today — only
against the reconciled doc's own imported claim.

## 1. Sufficiency check

The axiom is deliberately minimal: `Field K`, `NumberField K`,
`IsTotallyComplex K`, `finrank ℚ K ≥ 18` ⊢ `|(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K`.
It carries no tameness/ramification/conductor hypothesis. That is *correct*
factoring in principle — Odlyzko's bound is a pure statement about number
fields, and tameness-at-2/conductor-2 belongs to the consumer's derivation of
a matching *upper* bound on `discr K` for the field cut out by `ker ρ̄`. But:

- Grep across `FLT/GaloisRepresentation/HardlyRamified/{Defs,Frey,Lift,Family,
  ModThree,Threeadic}.lean` for `conductor`, `tame`, `discr`, `IsTotallyComplex`
  returns **zero hits**. The upper-bound half of the Fontaine argument (the
  half that would actually be compared against 8.25) does not exist anywhere
  in Lean or in blueprint prose beyond one sentence
  (`ch04overview.tex:104-108`: "flat at 3 and tame at 2 ... irreducible
  representation would cut out a number field whose discriminant violates the
  Odlyzko bounds"). No explicit constant is stated there.
- The reconciled doc's §2.1 asserts the comparison constant is
  `U = 2^(2/3) * 3^(3/2) ≈ 8.248377821991616`, giving a "razor-thin"
  0.0197% margin over 8.25. **This exact expression appears nowhere in the FLT
  repo** (blueprint or Lean) — confirmed by grep. It is imported from the
  reviewer's own recollection of Fontaine's/Poitou's argument, not reconciled
  against repo evidence, and is presented with a precision (16 decimal digits)
  that implies verification which did not happen against this codebase.
- The repo *does* contain a numerically similar-looking constant of the same
  shape, `2^(2/3) * 3^(7/8)`, in `FLT/NumberField/DiscriminantBounds.lean`
  (`rootDiscrBound_thirteen_lt`/`_fourteen_gt`, ≈ 4.178). This is a **different
  number** (different exponent on 3, roughly half in log-scale) used for an
  unrelated Minkowski-side threshold at degree 14, not a conductor-2 Fontaine
  bound at degree 18. The surface similarity (`2^(2/3) * 3^(exponent)`) is
  exactly the kind of thing that gets silently conflated between passes; here
  it appears the reconciled doc is not conflating them, but a future
  formalizer skimming both documents easily could.
- **Conclusion:** sufficiency of 8.25 for the actual consumer inequality is
  currently unverifiable in-repo. Treat the reconciled doc's "0.0016 margin"
  claim as an unsourced external import, not a reconciled fact, until someone
  states the conductor-2/tame-at-2 upper bound explicitly (in blueprint LaTeX
  with a citation, ideally) and checks it against 8.25 with the same rigor
  applied to the axiom side.

## 2. Vacuity traps

Checked the literal quantifier structure:
`axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K]
[IsTotallyComplex K] (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K`.

- Not vacuous over an empty domain: totally complex number fields of degree
  ≥ 18 demonstrably exist (e.g. suitable cyclotomic fields), so the hypothesis
  set is satisfiable and the axiom is a genuine (if GRH-free-strong) claim,
  not a degree-range emptiness trick.
- `|(discr K : ℝ)|` uses `abs` over the cast discriminant — standard,
  no sign-convention ambiguity; `NumberField.discr` is a bona fide nonzero
  integer for any number field, no junk-value risk from a partial/noncomputable
  default.
- `finrank ℚ K` is backed by the `NumberField K` instance (which already
  bundles finite-dimensionality), so there's no "junk `finrank = 0`" escape
  hatch for exotic `K`.
- The genuine vacuity risk is downstream, not in the axiom: `mod_three` is
  `sorry` and never mentions `Odlyzko_statement`, `NumberField`, or `discr`.
  Whoever eventually instantiates `K` (the fixed field of `ker ρ̄`, or of the
  *projective* representation — these differ by scalars and are easy to
  conflate) must independently prove `IsTotallyComplex K` and
  `finrank ℚ K ≥ 18` for the *correct* field. A wrong instantiation (e.g.
  quotienting by the wrong kernel, or picking a subfield with smaller degree)
  would not make the axiom vacuous, but would make the application unsound in
  a way Lean's type system cannot catch until someone writes the missing
  ~200 lines connecting `IsHardlyRamified` to an actual `NumberField` instance.
  This connective tissue is 100% unformalized today.

## 3. Degree-19 shortcut — stress test

The reconciled doc's own §3/PQ2 already declines to endorse raising 18→19
without a consumer lemma proving every relevant field has degree ≥ 19, which
I agree with. Additional finding that sharpens the risk: `DiscriminantBounds.lean`'s
`le_fourteen_of_rootDiscrBound` only reaches **n ≤ 14** from the Minkowski/tame
side (via the `2^(2/3)*3^(7/8)` threshold). Combined with the axiom's
`n ≥ 18` floor, degrees **15, 16, 17 are currently uncovered by any
formalized bound in this repo**, and this gap is not mentioned anywhere in the
reconciled map. Raising the Odlyzko floor to 19 would silently widen this
already-unaddressed gap to 15–18 rather than 15–17, compounding an existing
unverified hole instead of trading one clean threshold for another. Until the
15–17 gap is explicitly closed (or proven unreachable for the specific `k`,
`V` in `mod_three`), the degree-19 shortcut should be treated as strictly
worse than the status quo, not merely "not yet justified."

## 4. Panel questions — answers from this lens

- **PQ1 (Numdam reproducibility):** Out of this lens's direct scope (concerns
  proving the axiom, not consumer sufficiency), but note it cannot resolve the
  §2.1 margin dispute either, since that dispute is about a consumer-side
  constant (`2^(2/3)*3^(3/2)`) not derived from the Poitou table at all.
- **PQ2 (degree-19 consumer lemma):** Unresolved, and higher-stakes than
  stated — see §3. Do not approve M13 until (a) a degree-≥19 consumer lemma
  exists and (b) the 15–17 gap is independently closed or shown irrelevant.
- **PQ3 (FE route):** No finding from this lens; not a sufficiency/vacuity
  question.
- **PQ4 (Explicit-formula API freeze):** No finding from this lens.
- **PQ5 (Numerical Lean strategy):** Expand scope beyond certifying the
  axiom's own `8.25` at `n=18`. Before that number's tightness matters at all,
  someone must state and interval-certify the actual conductor-2/tame-at-2
  upper bound the `mod_three`/Fontaine argument will produce — a quantity that
  does not yet appear in Lean or blueprint with an explicit constant. Absent
  that, "sufficiency" of the axiom is a claim about a proof that has not been
  written down even informally with numbers attached.

File: `/Users/kas/FLT/cartography/panel/odlyzko-hypothesis.md` (working tree only, not committed).
