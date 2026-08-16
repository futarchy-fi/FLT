# Poitou 1977 — the PQ1 artifact, fetched and transcribed

**Author:** fermat (crew-18), 2026-08-16T14:33Z. **Resolves PQ1 in part** — see §5 for the
part that remains open.

## 1. Provenance

`odlyzko-reconciled.md` §4 PQ1 records: *"Obtain and check a committed page-image/PDF
artifact for Poitou p. 17 … the current environment could not fetch Numdam."* This
environment can.

| field | value |
|---|---|
| author | Georges Poitou |
| title | *Sur les petits discriminants* |
| venue | Séminaire Delange-Pisot-Poitou, Théorie des nombres, **18** (1976–77), no. 1, exposé 6 |
| pages | 18 pp. (paginated 6-01 … 6-18) |
| Numdam id | `SDPP_1976-1977__18_1_A6_0` |
| item page | https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/ |
| PDF | https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0.pdf — 1 884 833 bytes, `%PDF-1.4`, 18 pages, **carries an OCR text layer** |
| MR / Zbl | MR 551335 / Zbl 0393.12010 |
| companion | Poitou, *Minorations de discriminants (d'après A. M. Odlyzko)*, Séminaire Bourbaki 1975/76, exp. 479, LNM 567 |

The PDF is staged on crew-18 at `/home/agent/artifacts/poitou-1977-petits-discriminants.pdf`
and is **deliberately not committed to this repository**: it is a third-party scan and
redistribution terms are a decision for Kelvin, not for me. Anyone can re-fetch it with the
URL above; the transcription below is what the campaign actually needs.

## 2. The table (p. 18) — lower bounds on the root discriminant, totally imaginary fields

Heading, verbatim: *"Discriminants des corps totalement imaginaires"*, column `|d|^{1/n}`.
Transcribed from the OCR text layer.

| n | `|d|^{1/n} ≥` | | n | `|d|^{1/n} ≥` |
|---|---|---|---|---|
| 2 | 1.722119 | | 20 | 9.805700 |
| 4 | 3.254561 | | 22 | 10.257528 |
| 6 | 4.557067 | | 24 | 10.668331 |
| 8 | 5.659362 | | 26 | 11.043890 |
| 10 | 6.600341 | | 28 | 11.388914 |
| 12 | 7.412879 | | 30 | 11.707282 |
| 14 | 8.122437 | | 40 | 12.996001 |
| **16** | **8.748418** | | 60 | 14.670796 |
| **18** | **9.305672** | | 100 | 16.488963 |

(The published table continues to n = 360, ending 19.590361.)

## 3. THE CORRECTION — what `9.305672` actually is

`odlyzko-reconciled.md` node M10 currently reads:

> "evaluate a fixed `y` at `n=18` to at least `log 8.25` (the scan's optimized value is
> `9.305672`)"

**`9.305672` is not an optimizing `y`. It is the root-discriminant bound itself at n = 18** —
the `|d|^{1/n}` column of the p. 18 table. The two quantities were conflated somewhere in
the second-hand reading, and every downstream node inherited it.

The evidence is internal to the paper and checks exactly. Page 17 works the case `n = 8`,
`r₁ = 0`, and states the optimizing `y = 1.7242`, obtaining `(1/n)·log|d| > 1.733311` and
hence `|d|^{1/n} > 5.65936`. The table's `n = 8` row is `5.659362`, and
`exp(1.733311) = 5.659361`. So the column is the bound, the `y` values are order 1–20
(p. 16: *"jusqu'à 20"*), and `9.305672` sits in the bound column against `n = 18`.

## 4. Two consequences, both favourable, both changing the plan

### 4a. The margin at n = 18 is large — certify loosely, not tightly

The target axiom is `|d_K| ≥ 8.25 ^ n`, i.e. root discriminant `≥ 8.25`, i.e.
`log 8.25 = 2.110213`. Poitou gives `9.305672` at `n = 18`, i.e. `log = 2.230624`.

```
required   2.110213
achieved   2.230624
margin     0.120411   in log terms
ratio      1.1280x    12.8% headroom
```

`odlyzko-endgame-decomposition.md` §4 R5 already advised "pick margin over sharpness"; this
quantifies it. **The interval-arithmetic certification in R1/R2/R4/R5 has 12.8% of room**,
which is enormous by the standards of certified numerics — it means a coarse enclosure
suffices and the R4 truncation bounds can be generous. This materially de-risks the only
L-sized node in the chapter.

### 4b. The degree-18 contract has ~2 degrees of slack — and PQ2's pressure is *downward*

`8.25` is first exceeded at **n = 16** (`8.748418`), not n = 18. The table is monotone
increasing in `n` throughout its range.

PQ2 asks whether the axiom's threshold may be raised 18 → 19. This says the question is
pointed the wrong way: the method already delivers the required constant two degrees below
the contract, so **18 is comfortably safe and there is no numerical pressure to raise it**.
`odlyzko-reconciled.md` M13 — the "degree-19 closed-form shortcut" — is therefore an
optimization for a problem the numbers do not have. Recommend closing PQ2 in favour of
retaining 18, and dropping M13 from the plan unless it earns its place on other grounds.

Monotonicity in the table is also direct empirical support for node **S1**
(`odlyzko-endgame-decomposition.md` §5), whose whole content is that a fixed-`y` bound is
nondecreasing in `n`. The published values behave exactly as S1 asserts.

## 5. What is still open — PQ1 is resolved *in part*

**Resolved:** the artifact exists, is fetchable without credentials, is staged locally, and
its numerical content — the table, the n = 8 worked example, the optimizing `y` for that
case, and the equation-numbering structure — is transcribed above and internally
cross-checked.

**Not resolved: the displayed equations (19)–(26) are still not transcribed.** They are
typeset formulas rendered as images in the scan, and the OCR text layer captured only the
prose *between* them. What the text layer does establish is their role, which is worth
recording because it constrains node R3:

- **(19)** the primary series for the archimedean term; adequate for numerical use "disons
  pour n ≥ 100", with fewer useful terms as `n` grows;
- **(21)** supplies an approximate optimal `y`, close to the true optimum at large degree;
- **(22)** a simpler auxiliary series, convenient for small `y`, with an equivalent closed
  form convenient for larger `y`;
- **(23)** the approximation used to evaluate the worked example;
- **(25)** the practical inequalities *written in the totally imaginary case `r₁ = 0`* —
  exactly our case — with a stated accuracy loss of order `0.55·10⁻⁷`;
- **(26)** the final inequality, valid for every positive `y`, optimized at the minimum;
- **(13)** the base inequality that (26) re-expresses.

**To finish PQ1, someone needs to read pages 14–17 as images and transcribe the display
formulas.** I could not: `pdftoppm`/`poppler-utils` is absent from this pod and I lack the
privileges to install it (`pip install --break-system-packages pypdf` worked, which is how
the text layer was extracted; the system package did not). Any worker with poppler, or any
agent that can view the PDF pages, closes this in one session. **That is now the single
remaining blocker on nodes Q3′, R3 and — downstream of R3 — R4 through R7.**

Node **Q3** (Tartar's `g` and `F ≥ 0`) remains gated the same way: the paper's definition of
the auxiliary function is in the display formulas, not the prose. Keep Q3 stated over an
abstract `g` with its two properties as hypotheses, exactly as
`odlyzko-endgame-decomposition.md` §3 already specifies, and instantiate in Q3′ once the
transcription lands.

## 6. Provenance discipline

Everything in §2–§4 comes from the OCR text layer of a 1977 scan. OCR on a scanned French
typescript is not trustworthy digit-by-digit, and the campaign's numerical column will be
gated on these values. Two guards:

1. The `n = 8` cross-check in §3 (`exp(1.733311) = 5.659361` versus table `5.659362`) is an
   internal consistency test that would fail under most OCR digit corruption. It passes.
2. `odlyzko-reconciled.md` §4 PQ5 already directs the use of *conservatively recomputed*
   error bounds "until every printed Poitou decimal is independently certified". That still
   stands, and §4a's 12.8% margin is what makes it cheap to obey: **do not trust the printed
   digits, re-derive with slack.** The table's role is to tell us the answer is comfortably
   true, not to be cited as the proof.
