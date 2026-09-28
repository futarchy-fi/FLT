# MZ1: contracts for the prime-level Mazur route

Source/code review: 2026-09-28; FLT `6b0261b42f006644b966243ac348d2e726ac020c`,
Mathlib `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
This refines G1/G2 of [MAZUR_PLAN.md](MAZUR_PLAN.md). It supplies contracts,
not constructions of modular curves or a proof of the torsion exclusion.

## Route decision and the exact FLT requirement

Retain Mazur's prime-level proof, Chapter III §5, pp. 156–160.
The bounded second review found no complete shorter proof from the existing
semistability, hardly-ramified, or category-D endpoints. This is a source
review result, not a claim that a shorter proof is impossible.

There are three different interfaces:

1. The **actual Frey caller** needs `FreyIrreducibility` below: irreducibility
   only for `P.freyCurve`, for a `FreyPackage P` with `17 ≤ P.p`.
   `FLT/Proof.lean` and `FLT/Assembly/Proof.lean` combine this with the
   opposite conclusion from the hardly-ramified machinery.
2. The **current conditional assembly** accepts
   `FLT.Assembly.MazurTorsionExclusion`: exclusion of `(Z/2)^2 × Z/p` on
   **every** elliptic curve over Q. This is a sufficient, stronger interface.
3. The **selected arithmetic route** proves `NoLargePrimeTorsion`, excluding
   a point of prime order at least 17 on every rational elliptic curve.
   The already-proved adapter gives interface 2 and then interface 1.

A clean proof of interface 1 would therefore suffice to replace the Mazur
input after a small assembly rewire. One need not prove a universal torsion
classification. No such proof is supplied by this review.

### The provenance that the current counterexample forgets

`FLT/FreyCurve/Mazur.lean`, `mazurW_counterexample_of_reducible`, has two
branches after the two filtration characters are shown to include a trivial
character:

- A trivial subcharacter gives rational p-torsion on the original Frey curve.
- A trivial quotient gives rational p-torsion on a **different** curve using
  `quotient_curve_of_trivial_quotient`. Full two-torsion survives its map.

The latter theorem exports an elliptic curve and an additive homomorphism
on rational points whose kernel is killed by p. Its signature does **not**
export an isogeny of schemes, its degree, semistability of the target, or a
Frey package for that target. Its construction uses Vélu, but those stronger
conclusions need separate theorems; an arbitrary additive homomorphism
with p-killed kernel cannot substitute for them.

Thus “only exclude p-torsion on the original Frey curve” does not cover both
branches. A useful restricted alternative must cover the original curve
**and its relevant degree-p quotient**, preserving actual geometric
provenance. The smaller direct input `FreyIrreducibility` avoids choosing
an incomplete notion of isogeny orbit.

### Why the proposed shortcuts do not close it

| Candidate | Checked input and obstruction | Decision |
|---|---|---|
| Semistability plus full two-torsion implies hardly ramified | `HardlyRamified/Defs.lean` additionally requires unramifiedness outside `{2,p}`, finite flatness at p, and a quotient at two. Semistability alone allows multiplicative inertia at other bad primes. | Insufficient hypotheses. |
| Apply the existing theorem to the original Frey representation | `HardlyRamified/Frey.lean` proves it hardly ramified, then `torsion_not_isIrreducible` concludes **reducibility**. Rational p-torsion also gives reducibility. | No contradiction. |
| Apply category D to a reducible representation | `CategoryDClassification.lean` allows constant-three and multiplicative-three constituents; these are not forbidden. Its objects are three-primary over `Z[1/2]`. | Wrong conclusion and different prime/base. |
| Use lifting/compatible families to obtain irreducibility | `Assembly/Inputs.lean` starts lifting with irreducibility; `Assembly/PrimeField.lean` proves its negation. | Circular as a replacement for Mazur. |
| Bound torsion by reduction at 2 or 3 | `FreyCurve/Serre/AtTwo.lean` gives multiplicative reduction at 2. At split multiplicative reduction the component group can contain p-torsion. | No uniform local bound. |
| Use the special Frey discriminant at 2 | `two_pow_eight_mul_Δ_int` gives `v₂(Δ)=2p v₂(b)-8`, not divisible by p for p ≥17. This is promising for the original-curve branch, but degree-p Tate isogenies can multiply the valuation by p. | Does not exclude the quotient branch. |
| Composite level or a formal-immersion proof | An injected group supplies a point of order 2p, but not a ready classification of `X₁(2p)` or `X₀(2p)`. No such endpoint or formal-immersion package was found. | Adds missing global geometry. |

The `HardlyRamified/...` paths in this table are under
`FLT/GaloisRepresentation/`. The discriminant observation is a proposed
local subargument, not a newly proved Lean result. The source itself warns
that the indispensable Step 3 is global: Mazur, III §5, p. 158.
The conclusion does not rely on treating existing declarations as trusted
proofs of their transitive dependencies.

## Source ledger and corrections to MZ0

[M] B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS
47 (1977), 33–186, [DOI](https://doi.org/10.1007/BF02684339),
[full PDF](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf).
Page numbers below are **printed page numbers**. The downloaded Numdam PDF
includes an initial cover, so PDF page 2 is printed page 33.

| Contract / construction | Exact source read | Scope |
|---|---|---|
| G1 coarse moduli and smooth integral curve away from p | [M] II §1, pp. 62–64 | `X₀(p)` agrees with the coarse model away from p; do not claim a universal elliptic curve over it. |
| G1 two disjoint rational cusp sections | [M] II §1, p. 64 | Remain disjoint under base change. |
| G1 integral section and cusp orientation | [M] III §5, Step 3, p. 159 | Base `Spec Z[1/(2p)]`; identity component corresponds to **zero**, outside it to **infinity**. |
| G2 Hecke correspondences and Eichler–Shimura | [M] II §6, pp. 87–90 | Actual algebraic correspondences, not only analytic modular-form operators. |
| G2 Eisenstein ideal | [M] II §9, unnumbered definition, p. 95 | Generated by `1+w` and `1+l-T_l` for primes l different from p. |
| G2 quotient construction | [M] II §10, (10.3)–(10.4), pp. 97–98 | Quotient by the subvariety generated by the completion-kernel ideal, **not** by `I·J`. |
| G2 good integral model | [M] II §10, p. 98 | Néron–Ogg–Shafarevich gives an abelian scheme over `Z[1/p]`, hence over our base. |
| G2 rational finiteness | [M] III §3, Lemmas (3.2)–(3.4), Corollary (3.5), pp. 148–150 | Uses Mordell–Weil, finite-flat cohomology and completion/support arguments. |
| G2 nonzero cusp image | [M] introduction p. 35; III (3.1), p. 148; III §5, p. 160 | Full (3.1) gives order `numerator((p-1)/12)`; client only needs distinct images. |
| G2 nonconstant projection and finite curve points | [M] III (4.1), pp. 151–152 | Nontrivial quotient, curve image generates it; finite fibers plus finite target points. |
| Integral specialization of torsion | [M] III §5, pp. 159–160, footnote on p. 160 | Includes residue-characteristic-primary torsion at odd primes; cites Oort–Tate. |

Corrections: G1's modular-curve source is **II §1**, not I §1 (admissible
groups). The introduction's abbreviated G2 reading list refers to II §§6,
8, **10**, and Proposition 14.1; there is no proposed theorem “8.10”.
III §5 p. 159 prints a cross-reference “[7], VI, §5”; the relevant
moduli treatment is Deligne–Rapoport, listed as [9] in [M], and [M] II §1
identifies that source explicitly. Do not copy the inconsistent reference
as a checked independent citation.

[DR] P. Deligne and M. Rapoport, *Les schémas de modules de courbes
elliptiques*, LNM 349 (1973), 143–316. The construction dependencies are
II (generalized elliptic curves), IV (moduli and coarse spaces), VI §5
(cuspidal interpretation), VII §2 (cuspidal sections), as referenced in
[M]. Their precise independent page-level verification is a **construction
gate**, not something this bounded review claims to have completed; the
contracts above are directly supported by the checked pages of [M].
