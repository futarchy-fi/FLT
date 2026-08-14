# CBC chapter — literature-fidelity seat (hub-lsb1u.5.5)

Adversarial, lens: literature fidelity. Against `cartography/cbc-reconciled.md`.

## Findings

**(1) Prime-cyclic + solvable-by-iteration — REFUTED as characterized (sizing/soundness of D-8/S5).**
Langlands AM-96 proves existence (Prop. A) and descent (Prop. B: cuspidal `Π`
is a lift iff `Π^τ ~ Π`) only for cyclic `E/F` of **prime** degree ([IAS
text](https://publications.ias.edu/sites/default/files/book-ps.pdf)). Extending
descent to general cyclic/solvable towers is *not* free iteration: it required
Rajan, "On the image and fibres of solvable base change" (Math. Res. Lett. 9
(2002)) and L. Clozel–C.S. Rajan, "Solvable base change," [J. Reine Angew.
Math. 772 (2021) 147–174](https://arxiv.org/abs/1806.02513), which depend on
Lapid–Rogawski's classification (their Thm. 2) of `π` with `π^σ ≅ π⊗ω`, and
each descent step contributes a Hecke-character twist that must be tracked
across the tower. D-8/S5's framing ("Mathlib has the group theory," size
S/M, "no real conflict" in D5) undersells this: two dedicated papers, 22 and
41 years after Langlands, were needed to nail the solvable-tower descent/fiber
statement. The reconciled map's Q2 correctly flags tower-preservation as open,
but §5's sizing (S for S5, M for D-8) and D5's "no real conflict" resolution
are optimistic; cite Rajan 2002 + Clozel–Rajan 2021, not just "Langlands 1980
descent chapters," for D-6/D-8.

**(2) Satake-unramified-only sufficiency — UNVERIFIED (repo question, not literature dispute).**
Independently confirmed against the actual tex: `ch04overview.tex:86-88` and
`chtopbestiary.tex:212-214` name only "cyclic base change ... and
classification of image" plus multiplicity one/JL — no ramified local
identity is invoked in either sentence. This is a repo-grep fact, not
something literature refutes or confirms; Langlands' Property C fiber
description is itself stated globally (Hecke-character twist), consistent
with the slim reading. No refutation found.

**(3) Ramified Shintani cut — UNVERIFIED, independently reproduced.**
Re-grepped both invocation sites directly (not trusting the reconciled map's
quotes): confirmed neither mentions local ramified BC. This matches D3's
conclusion. Cannot be settled by literature alone since it's a claim about
what the *blueprint* needs, not what Langlands proves — Langlands' own
theorem (Ch. 2–3) does treat ramified/archimedean matching as machinery
internal to the proof (D-2's placement is right), so D3's "out of the
statement, in the deferred ledger" framing is literature-consistent.

**(4) σ-invariance descent — CONFIRMED, source pinned.**
Exact source: Langlands, *Base Change for GL(2)*, AM-96 (1980), Ch. 1,
**Property B**: an isobaric (in particular cuspidal) `Π` on `GL(2)/E` is a
base-change lift iff `Π^τ ∼ Π` for all `τ ∈ Gal(E/F)`; **Property C** gives
the fiber as a twist by characters of `F×\𝔸_F× ` trivial on norms from `E`
(≅ `Gal(E/F)^` via CFT), size `ℓ` generically, `1` in the exceptional
induced-from-`E` case at `ℓ=2`. This is stated for prime-cyclic `E/F` only;
general solvable case needs (1)'s extra citations. Reconciled map's S4/D-6
attribution to "Langlands 1980 descent chapters" is correct but should cite
Ch. 1 Properties B/C specifically, plus Lapid–Rogawski for the non-prime case.

**(5) AI-quadratic-CM scope — CONFIRMED.**
Literature basis is real and matches D-7's citation list: classical route is
Hecke 1926 theta series (holomorphic, imaginary-quadratic case — the one FLT
needs, weight 2); representation-theoretic version is Jacquet–Langlands 1970
[§12](https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/jl-ps.pdf)
(automorphic induction via Weil representation); Arthur–Clozel AM-120 Ch. 3
gives the general-`n` version. The JL-panel handoff (`71ae014`,
`jl-adjudication.md` Hole H1) explicitly assigns orphaned AI content to CBC's
S6 — verified this ruling exists and matches the reconciled map's claim; not
a fabricated citation.

## Panel questions (PQ), literature lens

1. Accept D-6/D-8 citations as pinned to Langlands Ch.1 Props B/C
   (prime-cyclic) + Rajan 2002 + Clozel–Rajan 2021 (solvable case), not a
   generic "Langlands 1980 descent chapters (literature-verify)."
2. Q2 (tower preservation) is *more* open than D5 admits: Clozel–Rajan's
   result is conditional ("under suitable conditions on the solvable
   extension") — the reconciled map should not resolve D5 as "no real
   conflict" until those conditions are checked against the Skinner–Wiles
   tower.
3. D-8's size M is too low given (1); recommend L, shared citation burden
   with (1)'s papers, and remove "Mathlib has the group theory" as if it
   settles the analytic content (it settles only the chief-series bookkeeping).
4. Q3 (Eisenstein edge): Langlands' own dichotomy (Prop. A: `Π` cuspidal
   unless `π` induced from an `E`-character) is the right literature anchor;
   S4's "exclude by hypothesis" is defensible per Property B/C's own scope.
5. Q4/Q5 not literature-adjudicable from this seat; defer to hypothesis/
   dependency seats.
6. AI-quad citation (5) stands; recommend adding Jacquet–Langlands §12
   page/theorem number and Arthur–Clozel Ch.3 theorem number before D-7 is
   promoted out of "(literature-verify)."

Sources: [Langlands AM-96 (IAS PDF)](https://publications.ias.edu/sites/default/files/book-ps.pdf) ·
[Clozel–Rajan, Solvable base change, arXiv:1806.02513](https://arxiv.org/abs/1806.02513) ·
[Clozel–Rajan, J. Reine Angew. Math. 772 (2021)](https://www.degruyterbrill.com/document/doi/10.1515/crelle-2020-0023/html) ·
[Jacquet–Langlands, Automorphic Forms on GL(2) (UBC archive)](https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/jl-ps.pdf) ·
[Arthur–Clozel AM-120](https://www.degruyterbrill.com/document/doi/10.1515/9781400882403/html)
