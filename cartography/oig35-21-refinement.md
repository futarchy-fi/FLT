# oig35.21 refinement — `ZeroTheoryN2.lean` (C2-CLOSURE-FIX)

Target: `FLT/NumberField/ZetaFE/ZeroTheoryN2.lean` (140 lines), at main `5f90401`.
Read-only analysis; no build performed (no toolchain or Mathlib on crew-18). Every
Mathlib name below was verified verbatim against the pinned rev
`bc06ce9f87cda9bf825ecab192b115685e629898`, except the three explicitly marked
**[CONFIRM]**.

## 0. The headline: this is not conversion damage

The packet was scoped as "wire `ZeroTheoryN2` into the build closure + module idiom",
and the 01:52Z/03:22Z reading was that `public import` / module semantics broke name
resolution. **That is not what happened.** `scripts/sorry_count.py --closure` at
`5f90401` reports `FLT.NumberField.ZetaFE.ZeroTheoryN2` outside the `lake build` import
closure, and `grep -rn ZeroTheoryN2 --include='*.lean'` finds no importer anywhere in
the tree — only the file's own `namespace`/`end`.

So this file **has never been compiled, by anything, at any point.** It was delivered by
hub-oig35.19 under an acceptance of `lake build` + `no-sorry-in-file`; `lake build`
passed vacuously (`lakefile.toml` globs the bare module names `FLT` and
`FermatsLastTheorem`, so it compiles exactly the import closure of `FLT.lean`), and
`no-sorry-in-file` passed because the file contains no `sorry` — it contains 140 lines
of never-type-checked proof instead.

The 124 `Ambiguous term` / 126 `unsolved goals` / 137 `type mismatch` errors are
therefore **the file's original defects, surfacing on first compilation**. They are not
regressions introduced by the idiom conversion, and no amount of `public import`
adjustment will reduce them. This changes the packet: .21 as scoped is a mechanical
wiring job whose acceptance silently assumes the file is correct modulo module syntax.
It is not.

**The two theorem statements are, however, mathematically correct** (checked by hand,
§4) — so the packet is salvageable and the statements do not need re-derivation. Only
the proofs must be rewritten.

## 1. STOP — the wiring must not land on its own

Adding the `public import` line to `FLT.lean` changes what `lake build` compiles, and
there are only three possible outcomes:

1. **Wiring + a complete repair, one merge.** Naive count stays 67, and the build now
   genuinely covers the file. This is the only good outcome.
2. **Wiring merged before the proofs are fixed.** `lake build` fails repo-wide.
   *Every* enrolled packet's build acceptance fails simultaneously — a fleet-stopping
   event, not a local failure.
3. **Wiring merged with the two lemmas stubbed to `sorry` to "unblock".** Naive goes
   67 → 69 and live 56 → 58, so every packet gated on `... | grep -qx 67` false-fails
   at once.

So: **.21 must deliver the import line and the proof repair as a single atomic branch**,
or outcome 3 must be taken deliberately and paired with a coordinated re-pin of the
baseline constant across all enrolled packets in the same motion. Do not let a partial
.21 merge.

If the fleet needs throughput now, outcome 3 taken *deliberately* is defensible and I
would recommend it over leaving the file orphaned: replace the two proof bodies with
`sorry`, wire the import, re-pin the baseline 67 → 69 everywhere in one commit. That
restores truthful accounting — the corpus then admits two open holes instead of
silently claiming two proved theorems it has never checked — and turns a hidden defect
into a tracked one with a normal delta `[-2,-2]` follow-up packet.

**Related gate bug:** the canonical `.19` envelope handed to me as the template
(`inbox/refinement-templates.json`) pins its `sorry-count` acceptance to
`grep -qx 71`. The baseline has been **67** since `b0fbbec`. Mirroring that template
field-for-field, as instructed, would propagate a stale constant into every new
contract. Use 67 (or 69 under outcome 3).

## 2. Root cause of the 124 `Ambiguous term` errors — lines 7–8

```lean
open Complex
open Real
```

`Gamma`, `sin`, `cos`, `sinh`, `cosh`, `exp`, `log` are all declared in **both**
namespaces. With both opened and no disambiguation, every unqualified occurrence is
ambiguous — that is essentially every mathematical token in the file (lines 27, 32, 33,
39, 41, 42, 44, 47, 53, 54, 57, 60, 64, 66, 77, 79, 81, 88, 95, 98, 101, 104, 107, 117,
118, 120, 122, 125, 129, 132, 136, 138). One two-line edit removes the entire class:

```lean
open Complex
open scoped Real      -- π notation only; does NOT bring Real.sin/Real.Gamma into scope
```

Lines 9–10 (`open Filter Topology`, `open scoped RealInnerProductSpace ComplexConjugate`)
and the line 5 `import Mathlib.Analysis.InnerProductSpace.Basic` are unused by either
lemma; drop them, both to cut noise and because every extra `open` is another
ambiguity source.

**Consequence for the statements.** With `open Complex` alone, the bare `sinh`/`cosh` on
the RHS of lines 27 and 118 resolve to `Complex.sinh`/`Complex.cosh`, which is wrong —
those right-hand sides must be **real**. Write them explicitly:

```lean
lemma Gamma_one_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 + I * t)‖ ^ 2 = π * t / Real.sinh (π * t) := by

lemma Gamma_one_half_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = π / Real.cosh (π * t) := by
```

## 3. Root cause of the bulk of the 137 `type mismatch` errors — lines 101–102, 136–137

```lean
have h_norm2 : ‖Gamma (1 + I * t)‖ ^ 2 = Gamma (1 + I * t) * Gamma (1 - I * t) := by
  rw [sq_norm, h_conj_prod]
```

Two independent hard errors:

**(a) The equation is ill-typed.** `‖z‖ ^ 2 : ℝ`; `Gamma _ * Gamma _ : ℂ`. There is no
coercion inserted because neither side is a coercion application — Lean reports a type
mismatch at the `=`. This `have` cannot elaborate as written, and everything downstream
of it (the final `rw` chains at lines 103 and 138) fails with it. This is the single
largest contributor to the 137 count.

**(b) `sq_norm` is not a Mathlib lemma.** The relevant verified facts at the pinned rev:

- `Complex.mul_conj (z : ℂ) : z * conj z = ↑(normSq z)` — RHS is a **coerced real**.
- `Complex.normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z`.
- `Complex.conj_I : conj I = -I`, `Complex.conj_ofReal (r : ℝ) : conj (r : ℂ) = r`.

The fix is to carry the coercion explicitly and descend to ℝ only at the very end:

```lean
have h_norm2 : ((‖Gamma (1 + I * t)‖ ^ 2 : ℝ) : ℂ)
    = Gamma (1 + I * t) * Gamma (1 - I * t) := by
  rw [h_conj_prod, Complex.mul_conj]
  norm_cast                      -- [CONFIRM] closes ↑(‖z‖^2) = ↑(normSq z);
                                 -- if not, `simp [Complex.normSq_eq_abs]` / `exact?`
```

and then finish the top-level real goal with `exact_mod_cast` (or
`Complex.ofReal_injective`) rather than `rw`. **Never state a `‖·‖^2` identity at type ℂ
without the explicit `((· : ℝ) : ℂ)` ascription** — that is the mistake in both lemmas.

## 4. Per-line defects

The math is right, so I give the intended derivation first; it is far shorter than what
is in the file.

**Lemma 1.** `Γ(1-it) = conj Γ(1+it)`, so `‖Γ(1+it)‖² = Γ(1+it)·Γ(1-it)`. Then
`Γ(1+it) = it·Γ(it)`, and reflection at `s = it` gives `Γ(it)·Γ(1-it) = π/sin(πit)`.
Hence `‖Γ(1+it)‖² = it·π/sin(πit) = it·π/(i·sinh(πt)) = πt/sinh(πt)`. **One** reflection
and **one** `Gamma_add_one` — the file uses three reflections and two `Gamma_add_one`s
and never assembles them.

**Lemma 2.** `‖Γ(½+it)‖² = Γ(½+it)·Γ(½-it) = Γ(½+it)·Γ(1-(½+it)) = π/sin(π(½+it))
= π/cos(πit) = π/cosh(πt)`. This one is nearly right in the file already; it fails only
on §2, §3 and item (H) below.

| line(s) | defect | fix |
|---|---|---|
| 7–8 | both `Complex` and `Real` opened → 124 ambiguities | `open Complex` + `open scoped Real` (§2) |
| 5, 9, 10 | unused imports/opens, extra ambiguity surface | delete |
| 27, 118 | bare `sinh`/`cosh` on a real RHS resolves to `Complex.*` | write `Real.sinh` / `Real.cosh` |
| 28–29 | `hRe`/`hIm` are never used | delete |
| 30–38, 59–76, 84–87, 106–113 | abandoned scratch reasoning left in comments, including self-contradicting lines ("No, Γ(1 - it) = …") | strip; keep one comment stating the §4 derivation |
| 32–33 (`h_ref`), 39–40 (`h_ref2`), 60–61 (`h_frac`), 64–66 (`h_conj`) | dead — never used by the final chain | delete |
| 41–43 vs 54–56 | `h_den` and `h_den2'` prove the **same** statement, and line 42 uses `sin_add_pi` forward while line 56 uses `.symm` — one of the two is necessarily wrong | keep one |
| 42 | **`rw [mul_add, mul_one, Complex.sin_add_pi]` cannot fire.** Verified: `Complex.sin_add_pi (x : ℂ) : sin (x + π) = -sin x` matches `sin (?x + π)`, but after `mul_add, mul_one` the term is `sin (π + π * (I * t))` — π **first**. `Complex.sin_pi_add` does **not** exist at this rev | `rw [mul_add, mul_one, add_comm, Complex.sin_add_pi]` |
| 47, 53, 104 | `Complex.sin_mul_I` is stated for `sin (z * I)`; the argument here is `π * I * t`, i.e. `(π * I) * t`, which is not of that shape. Separately the RHS mixes a **real** `Real.sinh` into a complex equation | reassociate to `(π * t : ℂ) * I` by `mul_comm`/`mul_assoc` first, then bridge with `Complex.ofReal_sinh`. **[CONFIRM]** the exact orientation (`sinh z * I` vs `I * sinh z`) with `exact?` — both defects hold either way |
| 49 | `I_ne_zero.mp` — `Complex.I_ne_zero : I ≠ 0` is a `Ne`, **not** an `Iff`; `.mp` is a type error | drop; get `sinh (π*t) = 0` from `mul_eq_zero` on `I * ↑(sinh (π*t))` |
| 52 | precedence: `exact ht (mul_eq_zero.mp hπt).resolve_left hπpos` parses as `ht ((…).resolve_left) hπpos` | `exact ht ((mul_eq_zero.mp hπt).resolve_left hπpos)` |
| 79–83 | **`Complex.Gamma_add_one` is verified to be `(s : ℂ) (h2 : s ≠ 0) : Gamma (s + 1) = s * Gamma s`.** Two errors: the `s ≠ 0` hypothesis is never supplied (arity/type error), and the conclusion is about `Gamma (s + 1)` while the goal has `Gamma (1 + I*t)` — `simpa [mul_comm, mul_left_comm, mul_assoc]` supplies only *multiplicative* lemmas and cannot reorder an **addition** | see block below |
| 88–94 | `rw [← h_ref_it]; congr 1` on a product generates factor-wise subgoals that do not follow; the trailing `field_simp`/`ring_nf`/`simp` cannot recover. A large share of the 126 unsolved goals | derive from `h_add_one_neg` + `h_ref_it` by `field_simp` with `-(I*t) ≠ 0` |
| 98–100, 132–135 | `rw [← Complex.conj_I, ← conj_ofReal]` — `←conj_I` rewrites `-I ↦ conj I`, and there is **no** `-I` in the goal `Gamma (1 - I*t) = conj (Gamma (1+I*t))`. The rewrite fails | see block below |
| 114–115, 129–130 | `simp [...]` immediately followed by `ring`: if `simp` closes the goal, `ring` is a hard "no goals to prove" error; if it does not, `ring` will not close a simp-normalized form | replace with a single `field_simp` + `ring`; never chain `simp` then `ring` |
| 123–127 | `rw [mul_add, Complex.sin_add]` already splits the sum, then `hsin` (125) re-states a `sin_add` about a *differently associated* term (`I * (π * t)` vs `π * (I * t)`) that no longer occurs in the goal | do the `mul_add` and the `π * (1/2) = π/2` normalization first, then a single `Complex.sin_add` |

**`Gamma_add_one`, corrected:**

```lean
have hit : (I * (t : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast ht)
have h_add_one : Gamma (1 + I * t) = I * t * Gamma (I * t) := by
  rw [add_comm]; exact Complex.Gamma_add_one _ hit
have h_add_one_neg : Gamma (1 - I * t) = -(I * t) * Gamma (-(I * t)) := by
  rw [sub_eq_add_neg, add_comm]
  exact Complex.Gamma_add_one _ (neg_ne_zero.mpr hit)
```

Note `sub_eq_add_neg` is required: `Gamma (1 - I*t)` is not syntactically
`Gamma (-(I*t) + 1)`.

**The conjugation step, corrected** (uses only verified names):

```lean
have hconj_arg : (starRingEnd ℂ) (1 + I * t) = 1 - I * t := by
  simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring
have h_conj_prod : Gamma (1 - I * t) = conj (Gamma (1 + I * t)) := by
  rw [← hconj_arg, Complex.Gamma_conj]
```

`Complex.Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s)` is unconditional
(verified), so no side goal appears. The same two-step works verbatim for `½ + it`.

## 5. Recommended packet shape

Do **not** re-issue this as a wiring packet. Issue it as a proof packet whose write set
is `FLT/NumberField/ZetaFE/ZeroTheoryN2.lean` **and** `FLT.lean` (the import line), with:

- `base_revision` = `5f90401430edb6307b10152863119d820848e752`
- acceptance `sorry-count` pinned to **67**, not 71
- an added acceptance that the file is now *in* the closure — otherwise this packet can
  pass exactly as vacuously as .19 did:

```bash
scripts/sorry_count.py --closure    # exits 1 if any FLT/ module is orphaned
```

That last line is the durable fix for the whole class. `--closure` already exists in the
repo and needs no Lean toolchain; wiring it into `flt-acceptance` closes the hole that
let 140 uncompiled lines merge green. **`FLT.MazurW` and `FLT.PoitouTate` are also
currently orphaned** — the same check will surface them, and the C1 packet's evidence
for `FLT/MazurW.lean` is thinner than its receipt implies for exactly this reason.

Routing: this needs a strong model. The repair is not mechanical — it is a rewrite of
two proofs against a coercion discipline that the original author never established.
`deepseek-v4-pro` with the §4 derivation quoted verbatim in the prompt is reasonable;
without the derivation it will flail the same way the original did.
