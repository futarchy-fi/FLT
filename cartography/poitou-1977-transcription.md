# Poitou 1977 — the PQ1 artifact, fetched and transcribed

**Author:** fermat (crew-18), 2026-08-16T14:33Z. **PQ1 completed 2026-09-07** — the
display equations and Tartar definitions are transcribed in §7.

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

## 5. Historical status before the 2026-09-07 completion

**Resolved:** the artifact exists, is fetchable without credentials, is staged locally, and
its numerical content — the table, the n = 8 worked example, the optimizing `y` for that
case, and the equation-numbering structure — is transcribed above and internally
cross-checked.

At that stage, the displayed equations (19)–(26) had not yet been transcribed. They are
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

That historical blocker is resolved in §7: pages 14–17 were rendered at 300 dpi, visually
checked, and the display formulas were transcribed and numerically cross-checked. PQ1 is
therefore complete, and Q3′ and R3 may now proceed from the recorded formulas.

Node **Q3** (Tartar's `g` and `F ≥ 0`) was initially kept abstract because the paper's
definition of the auxiliary function occurs in the display formulas, not the prose. The
concrete definitions needed for Q3′ are now recorded in §7.

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

## 7. PQ1 completion — display equations and Tartar data

This section was transcribed directly from 300 dpi renders of PDF pages 13–17
(manuscript pages 6-12 through 6-16). Decimal commas in the scan are written as decimal
points below. Hyperbolic `sh`, `ch` and `arc tg` are written `sinh`, `cosh` and `arctan`.
No unclear digit or symbol remained in the requested displays.

### 7.1 Base inequality — equation (13), manuscript p. 6-11

For `y > 0`, Poitou substitutes `f(x sqrt(y))` in the unconditional inequality and obtains

```math
\frac1n\log|d| \ge \gamma+\log(4\pi)+\frac{r_1}{n}
 -\int_0^\infty \{1-f(x\sqrt y)\}\,h(x)\,dx
 -\frac4n\int_0^\infty f(x\sqrt y)\,dx, \tag{13}
```

where

```math
h(x)=\frac1{\sinh x}+\frac{r_1}{n}\frac1{2\cosh^2(x/2)}
     =\frac{k(x)}{\cosh(x/2)}.
```

The scaling identity used immediately below (13) is

```math
\int_0^\infty f(x\sqrt y)\,dx=\frac1{\sqrt y}\int_0^\infty f(x)\,dx.
```

### 7.2 Tartar auxiliary function and the closed-form bound (16), manuscript p. 6-13

Poitou records Tartar's construction as follows. Start with

```math
v(t)=\max(1-t^2,0), \qquad
g(x)=\frac1{2\pi}\int_{-\infty}^{\infty}v(t)e^{-ixt}\,dt
    =\frac{2}{\pi x^3}(\sin x-x\cos x),
```

and put `f(x)=g(x)^2`. For the normalization `f(0)=1` used in the numerical series, this is

```math
f(x)=\left\{\frac3{x^3}(\sin x-x\cos x)\right\}^2.
```

Equivalently, if `w=v*v`, then for `0 <= u <= 2`,

```math
w(u)=-\frac1{30}(u^5-20u^3+40u^2-32), \qquad
f(x)=\frac9{16}\int_{-\infty}^{\infty}w(u)e^{-iux}\,du.
```

The construction has `B(f)=18\pi^2/125`. The resulting rounded inequalities are

```math
\frac1n\log|d|\ge \gamma+\log(4\pi)+1-8.317302\,n^{-2/3}
\quad (r_1=n),
```

```math
\frac1n\log|d|\ge \gamma+\log(4\pi)-6.860404\,n^{-2/3}
\quad (r_1=0). \tag{16}
```

### 7.3 Integral and Taylor series — equations (17), (19) and (21)

The quantity to estimate is

```math
\int_0^\infty \{1-f(x\sqrt y)\}\,h(x)\,dx. \tag{17}
```

Using

```math
\int_0^\infty x^k h(x)\,dx
 =2k!\left\{\lambda(k+1)+\frac{r_1}{n}\eta(k)\right\},
```

with

```math
\lambda(k)=1+3^{-k}+5^{-k}+\cdots=(1-2^{-k})\zeta(k),
```

```math
\eta(k)=1-2^{-k}+3^{-k}-4^{-k}+\cdots=(1-2^{1-k})\zeta(k),
```

Poitou obtains the alternating series

```math
2y|f''(0)|\left\{\lambda(3)+\frac{r_1}{n}\eta(2)\right\}
+\cdots
+(-1)^{k+1}2y^k|f^{(2k)}(0)|
 \left\{\lambda(2k+1)+\frac{r_1}{n}\eta(2k)\right\}
+\cdots . \tag{19}
```

For the normalized Tartar function, the even derivatives are

```math
(-1)^k f^{(2k)}(0)
=\frac{9\,2^{2k+3}}{(2k+1)(2k+3)(2k+4)(2k+6)}. \tag{20}
```

The approximate optimal scaling used for large degrees satisfies

```math
y^{3/2}\bigl(n\lambda(3)+r_1\eta(2)\bigr)=\frac{3\pi}{2}. \tag{21}
```

Poitou notes this small-`y` regime is relevant when
`n lambda(3) + r1 eta(2) >= 12 pi`.

### 7.4 The auxiliary function `L` — equations (22) and (23), manuscript p. 6-15

The simpler alternating series is

```math
L(y)=2y|f''(0)|+\cdots+(-1)^{k+1}2y^k|f^{(2k)}(0)|+\cdots, \tag{22}
```

or, after inserting (20),

```math
L(y)=\frac45y-\frac{144}{175}y^2+\cdots
+(-1)^{k+1}y^k
 \frac{9\,2^{2k+4}}{(2k+1)(2k+3)(2k+4)(2k+6)}+\cdots.
```

For values of `y` where the series is inconvenient, the equivalent closed form is

```math
L(y)=-\frac3{20y^2}+\frac{33}{10y}+2
+\left(\frac3{80y^3}+\frac3{4y^2}\right)\log(1+4y)
-\left(\frac3y+\frac{12}{5}\right)\frac1{\sqrt y}\arctan(2\sqrt y). \tag{23}
```

The series (22) converges for `|y| < 1/4`; (23) is the practical form for larger positive
`y`.

### 7.5 `L_1`, the totally imaginary truncation and equation (25)

The exact series definition preceding the practical bound is

```math
L_1(y)=L(y)+\frac13L\!\left(\frac{y}{3^2}\right)
 +\frac15L\!\left(\frac{y}{5^2}\right)+\cdots
 +\frac{r_1}{n}\left\{L(y)-L\!\left(\frac{y}{2^2}\right)
 +L\!\left(\frac{y}{3^2}\right)-\cdots\right\}. \tag{24}
```

In the campaign's totally imaginary case `r_1=0`, Poitou gives

```math
\begin{aligned}
L_1(y) <{}& L(y)+\frac13L(y/9)+\frac15L(y/25) \\
&+\frac45y\left(\lambda(3)-1-3^{-3}-5^{-3}\right)\\
&-\frac{144}{175}y^2\left(\lambda(5)-1-3^{-5}-5^{-5}\right)\\
&+\frac{128}{105}y^3\left(\lambda(7)-1-3^{-7}-5^{-7}\right)\\
<{}& L(y)+\frac13L(y/9)+\frac15L(y/25)\\
&+0.006762754\,\frac45y
-0.000088536\,\frac{144}{175}y^2
+0.000001502\,\frac{128}{105}y^3 .
\end{aligned} \tag{25}
```

The stated loss in this bound is of order

```math
0.55\times10^{-7}y^4.
```

### 7.6 Final inequality — equation (26), manuscript p. 6-15

Substitution into (13) yields, for every `y > 0`,

```math
\frac1n\log|d|\ge
\gamma+\log(4\pi)+\frac{r_1}{n}
-\frac{12\pi}{5n\sqrt y}-L_1(y). \tag{26}
```

At fixed `y` and `r_1=0`, `L_1(y)` is independent of `n`, and the only remaining
degree-dependent term is `-12 pi/(5 n sqrt(y))`. This is the source-level justification for
the fixed-`y` monotonicity packet.

### 7.7 Required internal consistency check

For the worked example `n=8`, `r_1=0`, `y=1.7242`, the paper obtains from (23) and (25)

```text
L(y)       < 0.5945682
(1/3)L(y/9)  < 0.0431595
(1/5)L(y/25) < 0.0103233
L1(y)      < 0.6571721
```

Using the last bound in (26),

```text
gamma + log(4*pi) - 12*pi/(5*8*sqrt(1.7242)) - 0.6571721
  = 1.73331102615303...

exp(1.73331102615303...) = 5.65936121413802...
```

Thus `(1/8) log|d| > 1.733311` and `|d|^(1/8) > 5.65936`, matching the table value
`5.659362` up to its printed rounding. This completes the PQ1 correctness gate.
