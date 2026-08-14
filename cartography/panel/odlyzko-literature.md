# Odlyzko chapter — adversarial panel note: literature + numerics fidelity (hub-lsb1u.6.12)

Reviewer target: `origin/cartography/odlyzko-reconciled:cartography/odlyzko-reconciled.md`
(context skimmed: `origin/cartography/odlyzko:cartography/odlyzko.md`,
`origin/cartography/odlyzko-b:cartography-b/odlyzko.md`).

Lens: try to refute the literature/numerical claims. Primary source obtained and
read directly this session — the earlier passes' "could not fetch Numdam" was an
environment limitation, not a real access barrier.

Source: G. Poitou, *Sur les petits discriminants*, Séminaire Delange-Pisot-Poitou
18 (1976/77), exp. 6, p. 1–17. Numdam item `SDPP_1976-1977__18_1_A6_0`.
- Landing page: <https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/>
- PDF (fetched and OCR'd/page-imaged this session): <https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0.pdf>

## Method

`curl`'d the PDF directly (1.88 MB, 18 PDF pages incl. Numdam cover), ran
`pdftotext -layout` for a first pass, then rendered pages to PNG at 200 dpi
(`pdftoppm -r 200`) and read the equation-bearing pages (manuscript pp. 6-11
through 6-16, i.e. PDF pages 12–17) as images, since the OCR text layer garbles
inline math. All arithmetic re-verified independently in Python.

## Per-claim verdicts

1. **p.17 table, n=18, GRH-free, value 9.305672 — VERIFIED, exact.**
   Read the table image directly (manuscript page "6-17", header "Discriminants
   des corps totalement imaginaires"). Transcribed rows: n=14 → 8.122437, n=16 →
   8.748418, **n=18 → 9.305672**, n=20 → 9.805700 — all four match the reconciled
   map and P2's transcription digit-for-digit. The table sits directly after
   §4 "Minorations explicites **sans hypothèse de Riemann**" and the surrounding
   prose ("l'hypothèse de Riemann généralisée est d'autant plus utile que le degré
   est plus grand") confirms this is the unconditional (GRH-free) table, not a
   GRH-conditional one. The reconciled map's characterization is correct.

2. **Closed-form inequality (16), ~8.2432 at n=18 — VERIFIED, and the constant
   6.860404 IS exactly reproducible (P2's "could not reproduce" is REFUTED).**
   Read equation (16) directly off the page image (manuscript p. 6-13):
   ```
   (16)  (1/n) log|d| ≥ γ + log 4π + 1 − 8.317302 n^(−2/3)   (case r₁ = n)
                       ≥ γ + log 4π − 6.860404 n^(−2/3)      (case r₁ = 0)
   ```
   Poitou's derivation (p. 6-12, eq. 15): constant = 3·(2·b·B(f))^(1/3), with
   b = 4λ(3) + (r₁/n)·(π²/3) (p. 6-13, eq. before lemma 5's b-formula) and, for
   the Tartar-optimal f, B(f) = 18π²/125 (p. 6-14, derived from
   g(x) = (2/πx³)(sin x − x cos x), f = g²). Recomputing in Python with
   λ(3) = (7/8)ζ(3) = 1.05179979... (so 4λ(3) = 4.20719916, matching Poitou's own
   printed intermediate value on p. 6-13 exactly):
   - r₁=0: `3*(2*4.20719916*18*π²/125)**(1/3)` = **6.860403968**, matching the
     printed **6.860404** to 8 significant figures.
   - r₁=n: `3*(2*(4.20719916+π²/3)*18*π²/125)**(1/3)` = **8.317301959**, matching
     the printed **8.317302** to 8 significant figures.
   Both printed constants are exactly reproducible from Poitou's own stated inputs.
   Evaluating at n=18: `γ + log(4π) − 6.860404·18^(−2/3)` → exp(...) = **8.243190175**,
   matching the reconciled map's "8.2431901746…" to 9 digits. n=19 → 8.539903738;
   n=20 → 8.821040540 — both match the reconciled map exactly.
   **Correction to the record:** P2's claim (odlyzko-b, lines 184-187) that it
   "could not fully reproduce" 6.860404 and instead got 6.8653 is wrong — this is
   a straightforward arithmetic slip on P2's part, not a genuine discrepancy in
   Poitou's paper. The reconciled map hedges by also reporting P2's 6.8653
   variant "for conservatism" (§2.1); that hedge is unnecessary. It doesn't change
   the reconciled map's bottom-line verdict (still below 8.25 and below U at
   n=18), so this is a correction, not a refutation of the reconciled map's
   conclusion.

3. **Series machinery (19)–(26) — VERIFIED structurally against the source.**
   Read all of manuscript pp. 6-13 through 6-15 as images. Confirmed eq. numbers,
   structure, and content match the reconciled map's description: (17)/(18) Taylor
   bracketing of `f(x√y)`, (19) the λ/η series with `4λ(3)=4.20719916...`
   printed explicitly, (20) the closed form for `f^(2k)(0)` under Tartar's
   function, (21) the asymptotic optimal-y equation, (22)-(25) the
   fast-converging `L(y)`/`L₁(y)` truncation with explicit error bound
   "0,55·10⁻⁷ y⁴", and critically:
   ```
   (26)  (1/n) log|d| ≥ γ + log 4π + r₁/n − 12π/(5n√y) − L₁(y)
   ```
   exactly as the reconciled map states.

4. **Fixed-y monotonicity trick (one n=18 evaluation covers all n≥18) — VERIFIED,
   confirmed directly from eq. (26) and (24).** For r₁=0, eq. (24) defining L₁(y)
   reduces to `L(y) + (1/3)L(y/9) + (1/5)L(y/25) + ...` — the `(r₁/n){...}`
   correction term vanishes entirely, so **L₁(y) has no n-dependence** at fixed y
   when r₁=0. The only n-dependent term left in (26) is `−12π/(5n√y)`, which is
   monotonically increasing (toward 0) in n for fixed y > 0. So fixing y at its
   n=18-optimal value and increasing n only strengthens the bound. The reconciled
   map's claim is exactly right and is now source-verified, not inferred.

5. **U = 2^(2/3)·3^(3/2), 0.0197% margin, 12.8% headroom — VERIFIED by direct
   computation** (independent of Poitou, pure arithmetic):
   - `2**(2/3) * 3**(3/2)` = 8.248377821991616 (matches reconciled map exactly).
   - `8.25 − U` = 0.0016221780083842674 = 0.0196666...% of U (reconciled map
     rounds to "0.01967%"/"0.0197%" — consistent).
   - `9.305672/8.25 − 1` = 0.1279602424... = 12.7960...% (matches "12.7960%"
     exactly).

6. **Minkowski asymptote (π/4)e² ≈ 5.80 — VERIFIED.** `(π/4)*e**2` =
   5.803351089340846 (matches "5.80335…"/"≈5.80"). At n=18, the formalized bound
   `(π/4)·n²/(n!)^(2/n)` = 4.460409973307885, matching "≈4.46041" (A2) and P1's
   "≈4.46".

## Panel questions (this lens)

- **PQ1 (Numdam reproducibility) — effectively answered/closed.** The paper is
  fetchable (no DNS/access barrier from this environment), and I independently
  reproduced: the p.17 table's n=14/16/18/20 rows, eq. (16)'s two constants from
  first principles (b, B(f)), and eq. (26)'s exact form. Recommend: commit the
  four relevant page renders (or at least the table page and eq.-16/26 pages) as
  a checked-in artifact under `cartography/` so future passes don't need network
  access; I did not commit anything (working-tree-only instruction), so this
  artifact does not yet exist in the repo.
- **PQ5 (numerical Lean strategy)** — no need to carry P2's "conservative" 6.8653
  as a fallback; 6.860404 is exact from Poitou's own stated b and B(f), so a Lean
  formalization of M10 should target the printed constant directly (with an
  interval encasing the λ(3)/π² inputs), not a deliberately loosened one.
- PQ2–PQ4 are Lean-interface/blueprint questions outside this lens (no literature
  or numerics content to check); not addressed here.

## Worst refutation found

P2's claim (carried into the reconciled map's §2.1 as a hedge) that Poitou's
printed constant 6.860404 in eq. (16) "could not be reproduced" and is better
approximated by 6.8653 is **wrong** — 6.860404 reproduces exactly from Poitou's
own printed b = 4λ(3) = 4.20719916 and B(f) = 18π²/125. This does not overturn
any conclusion (all downstream numerics still hold under the correct, tighter
constant), but the reconciled map should drop the "more conservative
recomputation 6.8653" sentence in §2.1 as based on an arithmetic error, not a
genuine source ambiguity.

## Overall verdict

**SOUND**, no repairs needed to the reconciled map's conclusions. Every
literature citation (table digits, equation numbers, equation (16) and (26)
forms, the monotonicity argument) and every numerical claim I could check
(margin, headroom, Minkowski asymptote, both eq.-16 constants) verified exactly
against the primary source or by direct computation. The one correction is
cosmetic: the map's defensive hedge citing P2's unreproduced 6.8653 should be
removed since 6.860404 is in fact exactly reproducible and is the correct,
tighter constant to use.
