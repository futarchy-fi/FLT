# Odlyzko R1 riders — Dickson pin, tame-monotonicity recheck, and the residual dihedral case

Bead `hub-lsb1u.6.16` (+ R1 riders). Author: Fable, 2026-08-16. Working tree
only, not committed. Companion to `cartography/odlyzko-r1.md` (whose §4 this
file audits and extends) and `cartography/panel/odlyzko-adjudication.md`.
Repo ground truth read on `main` (148c849):
`FLT/Assumptions/Odlyzko.lean`, `FLT/NumberField/DiscriminantBounds.lean`,
`FLT/GaloisRepresentation/HardlyRamified/{Defs,ModThree}.lean`,
`FLT/Slop/PGL2/FiniteSubgroups/*.lean` (12 files, see §1.4 — a load-bearing
discovery).

## 0. Summary of verdicts

- **Weak link A (Dickson / degree ≥ 24): CORRECT, now pinned to primary
  sources, with one precision repair.** The wild case (`3 ∣ |im ρ̄|`,
  irreducible) forces `|im ρ̄| ≥ 24 ≥ 18`. But the R1 §4 route "irreducible
  + unipotent ⇒ contains SL₂(𝔽₃)" as stated skips the char-3 exceptional
  branch: for `p = 3` the classification of `p`-irregular subgroups of
  `PGL₂(𝔽̄₃)` includes an **A₅ class** absent for `p ≥ 5` (Faber Thm 6.1;
  see §1.2). The degree-24 arithmetic survives in every branch (§1.3).
  **Bonus finding: Dickson's classification is already formalized,
  sorry-free, in this repo** (`FLT/Slop/PGL2/FiniteSubgroups/`,
  `Dickson.dickson_classification`, with the `p = 3` A₅ branch handled
  correctly in `classification_wild_slop`), so the Lean cost of weak link A
  drops from L to S-remaining (§1.4).
- **Weak link B (large-e₃/general-k monotonicity): the sketch as written
  does NOT close.** It has (i) a genuine mathematical hole — the
  `|im ρ̄| ≥ 2e₃` step fails for `k`-irreducible **abelian** images inside a
  nonsplit torus, where only `|im| ≥ e₃` holds and the Minkowski numbers
  fail (`rootDiscrBound 10 ≈ 3.83 < 4.267`) — and (ii) two numeric slips
  (`rootDiscrBound 21 ≈ 4.597 < 4.60`, the 4.60 threshold is passed at
  n = 22 not 21; the 4.76 threshold is already passed at n = 26). **Repair:
  Raynaud's theorem closes the whole case in 5 lines** — flatness at 3 with
  `e = 1 < p − 1 = 2` forces `e₃ ∣ 8` for *every* finite residue field `k`,
  so the tame case always has `rd(K) ≤ 2^(2/3)·3^(7/8)` and degree ≤ 13 via
  the already-formalized `rootDiscrBound_lt_iff_lt_fourteen`. The
  monotonicity sub-argument becomes unnecessary (§2).
- **Residual case (tame small image, degree ≤ 13): reduces to ONE quadratic
  field and ONE trivial ray class group, and is thereby ruled out
  completely.** Field: `F = ℚ(√−3)` (the only quadratic field unramified
  outside 3 — the `√±1/√±2/√±6` fields guessed in the tasking do not arise,
  because a prime-to-3 image forces `ρ̄` unramified at 2). What must
  vanish: the ray class group of `F` with modulus `λ = (√−3)`, which is
  trivial (`h(F) = 1` and the unit `−1` generates `(𝒪_F/λ)^× ≅ 𝔽₃^×`).
  Hence the inducing character `ψ` is trivial and `ρ̄ ≅ 1 ⊕ ε₋₃` is
  reducible — contradiction (§3). This is exactly Serre's classical `p = 3`
  companion to Tate's mod-2 letter (Serre, Œuvres III, note 229.2, p. 710).
  Lean cost of the finite check: **S** (class-number-one of `ℚ(ζ₃)` via
  Mathlib's Minkowski-bound tooling + a 2-element unit computation); full
  discharge of the residual branch: **M** (CFT-free bridge lemmas, §3.5 —
  Mathlib has `NumberField.classNumber` but **no ray class groups**, so the
  bridge must be run through Kummer theory + in-repo `rootDiscrBound`).

---

## 1. Weak link A: the Dickson citation and the degree-24 arithmetic

### 1.1 What R1 §4 claims

"An irreducible subgroup of `GL₂(k̄₃)` containing a nontrivial unipotent
contains `SL₂(𝔽₃)` (Dickson's theorem), so `|im ρ̄| ≥ 24`," cited as
"standard (e.g. Suzuki, or Serre Prop. 15/16-style arguments)" and logged
UNVERIFIED-as-primary-source in the R1 ledger.

### 1.2 The pinned statements

**Primary source.** L. E. Dickson, *Linear Groups with an Exposition of the
Galois Field Theory*, Teubner, Leipzig, 1901 (Dover reprint 1960),
**§§239–261** (the subgroup classification; §260 is the summary paragraph).
The definitive modern write-up, which follows and credits Dickson's
§§239–261 explicitly and works over an *arbitrary* field of characteristic
`p`, is:

> **X. Faber, "Finite p-irregular subgroups of PGL₂(k)", La Matematica 2
> (2023), 479–522, DOI 10.1007/s44007-023-00051-4; arXiv:1112.1999.**
> **Theorem 6.1** (k algebraically closed of characteristic p): every
> finite subgroup of `PGL₂(k)` of order divisible by `p` is (up to
> conjugacy) one of: (i) `PSL₂(𝔽_q)` or `PGL₂(𝔽_q)`, `q = p^m`;
> (ii) a `p`-semi-elementary group — unique normal Sylow-`p` subgroup with
> cyclic quotient, i.e. **contained in a Borel** (these fix a point of
> `ℙ¹`, so are the reducible ones); (iii) dihedral (only for `p = 2`);
> (iv) **`A₅` (only for `p = 3`, present iff `𝔽₉ ⊆ k`)**.
> [VERIFIED-with-URL: statement read off the ar5iv rendering of
> arXiv:1112.1999 (Theorems A, B, 6.1) on 2026-08-16,
> https://ar5iv.labs.arxiv.org/html/1112.1999; Dickson §§239–261 credited
> in Faber's introduction and §§3–6.]

**Modern reference in the Galois-representation tradition.** J.-P. Serre,
"Propriétés galoisiennes des points d'ordre fini des courbes elliptiques",
Invent. Math. 15 (1972), 259–331, DOI 10.1007/BF01405086, **Proposition
15**: a subgroup of `GL₂(𝔽_p)` of order divisible by `p` either contains
`SL₂(𝔽_p)` or is contained in a Borel subgroup. (Companion Prop. 16 is the
prime-to-`p` list: cyclic, dihedral, A₄, A₅ — plus S₄ in `PGL₂`.)
[VERIFIED-as-cited: this exact usage is quoted in multiple secondary
sources, e.g. Stein et al., BSD verification notes,
https://wstein.org/sage_summer/bsd_comp/bsd01.pdf ("By Proposition 15 of
[Ser72], G either contains SL₂(F_p) or is contained in a Borel subgroup of
GL₂(F_p)"); the Springer scan itself is paywalled, so the verbatim French
text was NOT re-read — flagged. For our purposes Serre's Prop 15 is only
safe for `k = 𝔽₃` literally; for general `k` use Faber Thm 6.1, which is
open-access and includes the A₅ exception.]

### 1.3 The degree-24 arithmetic — CHECKED, with the honest proof route

Setting: `ρ̄ : G_ℚ → GL₂(k)` irreducible hardly-ramified, char `k` = 3,
`det ρ̄ = χ̄₃` (image `{±1}`), wild case `3 ∣ |im ρ̄|`. Write
`H = projective image ⊆ PGL₂(k̄)`.

1. Scalars in `GL₂(k)` have prime-to-3 order, so `3 ∣ |H|`: `H` is
   3-irregular.
2. `H` is not contained in a Borel: a Borel-contained projective image
   fixes a point of `ℙ¹(k̄)`, i.e. `ρ̄ ⊗ k̄` has a stable line; combined
   with `3 ∣ |im|` (giving a unipotent, hence a *unique* fixed line for the
   Sylow-3) this contradicts irreducibility. (Over `k` vs `k̄`: a
   `k̄`-stable line fixed by all of `im` and unique is Galois-stable hence
   `k`-rational; irreducible over `k` suffices.)
3. Faber Thm 6.1 then leaves: `H ⊇ PSL₂(𝔽₃) ≅ A₄` (the `q = 3` case,
   sitting inside every `PSL₂(𝔽_{3^m})`, `PGL₂(𝔽_{3^m})`), **or `H ≅ A₅`**
   — and `A₅ ⊃ A₄` too. So in every branch `H` contains a copy of `A₄`,
   `|H| ≥ 12`.
4. **`A₄` does not lift to `GL₂(k̄)` in characteristic 3** (this replaces
   the "contains SL₂(𝔽₃)" invocation and is 6 elementary lines): if
   `G₀ ⊆ GL₂(k̄)` maps isomorphically to an `A₄ ⊆ PGL₂`, its Klein
   subgroup `V₄ = {1, a, b, ab}` is projectively faithful, so `a, b, ab`
   are non-scalar involutions, each with eigenvalues `{1, −1}`, i.e.
   `det = −1`. But `det(ab) = det(a)det(b) = +1`. Contradiction.
5. Hence the preimage in `im ρ̄` of the `A₄` from step 3 meets the scalars
   nontrivially, so has order ≥ 2·12 = 24: **`[K : ℚ] = |im ρ̄| ≥ 24 ≥ 18`**
   ✓, and the Odlyzko axiom applies with the §1-of-R1 Fontaine bound
   `8.2484 < 8.25`. (For `k = 𝔽₃` one can say more: the preimage of `A₄`
   in `GL₂(𝔽₃)` is exactly `SL₂(𝔽₃)` — order 48 for `im ρ̄` once det is
   onto `{±1}` — so R1's literal claim was true over `𝔽₃`; the A₄-non-
   lifting form is what generalizes cleanly and is the right Lean target.)

[DERIVED from the VERIFIED Faber statement; steps 1–5 recomputed here.
Note the abstract-group fact "central extension of A₄ with no A₄ splitting
contains 2.A₄ ≅ SL₂(𝔽₃)" (Schur multiplier ℤ/2) is TRUE but NOT needed —
step 4–5 avoids it.]

### 1.4 Formalization state — Dickson is DONE in-repo

`FLT/Slop/PGL2/FiniteSubgroups/` contains a complete, **sorry-free**
(grep-verified: 0 `sorry` across all 12 files, ~590 KB) port of Duxing
Yang's DicksonClassification project (author header: Duxing Yang, 2026):

- `DicksonClassification.lean`: `Dickson.dickson_classification` — for odd
  `p`, every finite subgroup of `PGL₂(𝔽̄_p)` is cyclic / dihedral / A₄ /
  S₄ / A₅ / elementary-abelian-⋊-cyclic / `PSL₂(𝔽_{p^m})` /
  `PGL₂(𝔽_{p^m})`.
- `WildClassification.lean` line 694: `classification_wild_slop` — the
  `p ∣ |G|` case with the exceptional disjunct **`(p = 3 ∧ G ≃* A₅)`**
  exactly matching Faber Thm 6.1. (Independent confirmation that the A₅
  branch is real, and that the repo already knows it.)
- Plus `TameClassification`, `RecognitionA5`, `PSLRecognition`, etc.

Remaining Lean cost for weak link A given this: the two glue lemmas
(step 2: Borel ⇔ reducible for the *representation*; step 4/5: A₄
non-lifting ⇒ `|im| ≥ 24`), both elementary — **grade S** (was L before
the Slop discovery). Style-porting the Slop files to mathlib conventions is
a separate chore already flagged in the files' own headers.

---

## 2. Weak link B: the tame/large-e₃ monotonicity sketch

### 2.1 Audit of the sketch as written (R1 §4, tame bullet)

Claim under audit: for general finite `k`, if `e₃ > 8` then
`|im ρ̄| ≥ 2e₃ ≥ 20` while `rd(K) ≤ 2^(2/3)·3^(1−1/e₃) < 4.7622`, and
`rootDiscrBound n` "passes 4.60 by n = 21 and 4.76 by n = 27".

**Numeric slips (recomputed against the repo's
`rootDiscrBound n = (π/4)·n²/(n!)^(2/n)`):**
`rootDiscrBound 21 = 4.5975 < 4.60` — the 4.60 level is passed at **22**
(`4.6371`), not 21; and the 4.7622 level is passed already at **26**
(`4.7696`), not 27. Cosmetic, but the printed pair (21, 27) is wrong.

**The real hole.** `|im ρ̄| ≥ 2e₃` is justified by "irreducible-nonabelian
image versus the torus normalizer". But `mod_three` (Lean statement
re-read: `ModThree.lean` demands a `G_ℚ`-stable line *over `k`*) negates
irreducibility **over `k`, not over `k̄`**. A subgroup of a *nonsplit*
torus `𝔽_{q²}^× ⊆ GL₂(𝔽_q)` is abelian yet `k`-irreducible; for such an
image `|im| ≥ e₃` is all one gets. There the numbers genuinely fail: with
`e₃ = 10`, `n = |im| = 10` is possible a priori, and
`rootDiscrBound 10 = 3.832 < 2^(2/3)·3^(9/10) = 4.267`. No Minkowski
contradiction. (For honest nonabelian dihedral images the sketch's numbers
do close after the slip-fix: `rootDiscrBound(2e₃) > 2^(2/3)·3^(1−1/e₃)`
holds at `e₃ = 10` (4.556 > 4.267), `e₃ = 11` (4.637 > 4.310), and for
`e₃ ≥ 13` since `rootDiscrBound 26 = 4.7696 > 4.7622 > cap`. So the
sketch is salvageable for that sub-case, but not for the abelian one.)

**Verdict: does not close as written.** The abelian nonsplit-torus escape
route survives the sketch and would have to be caught by the §3 dihedral
analysis at unbounded degree — ugly. The right repair is upstream:

### 2.2 The repair: Raynaud kills large e₃ outright (the 5-line argument)

> **M. Raynaud, "Schémas en groupes de type (p, …, p)", Bull. Soc. Math.
> France 102 (1974), 241–280**, Théorème 3.4.1 / Corollaire 3.4.3–3.4.4
> (Numdam: https://www.numdam.org/article/BSMF_1974__102__241_0.pdf): for
> `𝒪_K` of mixed characteristic with absolute ramification `e < p − 1`, a
> finite flat group scheme over `𝒪_K` killed by `p` is a successive
> extension of `𝔽_{p^d}`-vector-space schemes, and tame inertia acts on
> each simple piece through a fundamental character of level `d` raised to
> the power `Σ aᵢ pⁱ` with all `aᵢ ∈ {0, …, e}` — i.e. **`aᵢ ∈ {0, 1}`
> when `e = 1`**. [VERIFIED via secondary sources read 2026-08-16: Stanford
> Mordell seminar notes L07 (M. Matchett Wood) and L08 (R. Bellovin),
> http://virtualmath1.stanford.edu/~conrad/mordellsem/Notes/L07.pdf and
> .../L08.pdf, and the paraphrase in arXiv:1109.6676 §Raynaud; the Numdam
> scan is the primary anchor but was not OCR-read verbatim — flagged at the
> same confidence level R1 assigned its "textbook tameness" steps.]

The argument, properly written (replaces the whole large-e₃ bullet):

1. The flat clause of `IsHardlyRamified` puts `ρ̄|_{G_{ℚ₃}}` on a finite
   flat group scheme `J/ℤ₃` killed by 3; here `p = 3`, `e = e(ℚ₃) = 1`,
   and `e = 1 < 2 = p − 1`, so Raynaud 3.4.3 applies (no hypothesis on `k`).
2. In the tame-at-3 case, `ρ̄(I₃)` has prime-to-3 order, hence acts
   semisimply on `V ⊗ k̄`, which is therefore a sum of the Jordan–Hölder
   inertia characters of step 1.
3. `dim V = 2`, so only levels `d ∈ {1, 2}` occur; a level-`d` fundamental
   character has order `3^d − 1`, and with exponents `aᵢ ∈ {0,1}` every
   occurring character has order dividing `3² − 1 = 8` (level 1: divides 2).
4. Hence `e₃ = |ρ̄(I₃)| = lcm` of those orders **divides 8 for every finite
   `k`** — the `k = 𝔽₃` conclusion of R1 §4, now unconditionally.
5. So tame-at-3 always gives `rd(K) ≤ 2^(2/3)·3^(7/8) = 4.1511`, and the
   already-formalized `rootDiscrBound_lt_iff_lt_fourteen` +
   `rootDiscrBound_strictMono` (`DiscriminantBounds.lean` 113–193) force
   `[K:ℚ] ≤ 13`. The large-e₃ sub-case, the `2^(2/3)·3^(1−1/e₃)` cap, the
   `|im| ≥ 2e₃` lemma, and both slipped constants all become unnecessary. ∎

(Interface note: what `DiscriminantBounds.lean` does *not* yet contain is
the consumer link "`K` totally complex ⇒ `|disc K|^{1/n} ≥ rootDiscrBound n`"
— Minkowski's actual bound. Mathlib's
`NumberField.exists_ideal_in_class_of_norm_le` / Hermite–Minkowski material
provides the ingredients; grade S–M, same connective-tissue class as R1 §3.)

---

## 3. The residual case: tame at 3, `3 ∤ |im ρ̄|`, degree ≤ 13

Standing hypotheses: `ρ̄ : G_ℚ → GL₂(k)` hardly ramified, irreducible over
`k`, char `k` = 3, and `3 ∤ |im ρ̄|` (the complement of §1's wild case; by
§2 its kernel field `K` has `[K:ℚ] = |im ρ̄| ≤ 13`).

### 3.1 First reduction: `ρ̄` is unramified outside 3

By R1 §1.3 (hardly-ramified clause at 2 + det unramified at 2), `ρ̄(I₂)`
is unipotent, of order 1 or 3. Its order divides `|im ρ̄|`, which is prime
to 3. So `ρ̄(I₂) = 1`: **`ρ̄`, and hence `K/ℚ`, is unramified outside 3**,
and tame at 3. [DERIVED — 3 lines. This is the observation that collapses
the tasking's guessed list `ℚ(√±3), ℚ(√±1), …` to a single field, and it
places the residual case verbatim inside the classical theorem:]

> **Classical antecedent.** "There is no continuous irreducible 2-dim
> mod-`p` representation of `G_ℚ` unramified outside `p`" — proved for
> `p = 2` by J. Tate, *The non-existence of certain Galois extensions of ℚ
> unramified outside 2*, Contemp. Math. 174 (1994), 153–156 (1973 letter to
> Serre), and for **`p = 3` by Serre: Œuvres III, note 229.2, p. 710**
> (Springer 1986), by the same discriminant-bound-plus-CFT method.
> [VERIFIED-as-cited via arXiv:2108.07577 (Dieulefait–Pacetti, simplified
> Serre-conjecture proof) and arXiv:2509.00635, both crediting exactly
> these loci, read 2026-08-16.] The residual case is precisely the
> small-image half of Serre's note; what follows is that argument made
> explicit against the repo's interfaces.

### 3.2 Second reduction: `ρ̄` is induced from (or split by) `F = ℚ(√−3)`

`3 ∤ |im ρ̄|` makes the projective image `H` 3-regular; by Dickson's
prime-to-`p` list (Faber Thm C / Serre Prop. 16, both cited in §1.2;
in-repo: `classification_tame_slop`) `H` is cyclic, dihedral, A₄, S₄ or
A₅. The last three have order divisible by 3 — excluded. So `H` is cyclic
or dihedral, i.e.:

- **`H` cyclic** ⇒ `im ρ̄` abelian ⇒ (irreducible over `k`, so not
  `k`-split) `im ρ̄` lies in a nonsplit torus and
  `ρ̄ ⊗ k̄ ≅ ψ ⊕ ψ^σ` for a *global* character `ψ : G_ℚ → k̄^×`,
  `σ = Frob_{|k|}` acting on values, `ψ^σ ≠ ψ`.
- **`H` dihedral** ⇒ `im ρ̄` normalizes a torus; the index-2
  torus-preimage subgroup fixes a quadratic field `F ⊆ K` and
  `ρ̄ ≅ Ind_{G_F}^{G_ℚ} ψ` with `ψ : G_F → k̄^×`, `ψ ≠ ψ^c`
  (`c` = conjugation). [Standard dihedral dichotomy; Serre 1972 §2.6
  Prop. 16 for the list, e.g. Darmon–Diamond–Taylor §2.6 for the induced
  form.]

In the dihedral case `F ⊆ K` is a quadratic field unramified outside 3
(§3.1). The only such field is **`F = ℚ(√−3)`**: a quadratic field of
discriminant `±3^a` must have squarefree-or-`4d` discriminant `−3`
(`disc ℚ(√3) = 12` is ramified at 2; `−3 ≡ 1 mod 4` ✓). [DERIVED —
elementary.] Consistency: `det ρ̄ = χ̄₃ = ε₋₃` already forces
`ℚ(√−3) ⊆ K`.

In both cases `ψ` factors through `Gal(K/F)` (resp. `Gal(K/ℚ)`): its
kernel contains `ker(ρ̄|_{G_F})` since `ψ` is a Jordan–Hölder character of
`ρ̄|_{G_F}`. So `ψ` has finite order prime to 3, cuts out `M ⊆ K` with
`M/F` **abelian, unramified outside `λ = (√−3)`, and tame at `λ`** (order
prime to residue characteristic ⇒ wild inertia, pro-3, dies).

### 3.3 The class-field-theory kill

**The finite check.** Let `Cl_λ(F)` be the ray class group of
`F = ℚ(√−3)` with modulus `𝔪 = λ = (√−3)` (no archimedean component: `F`
is imaginary). From `1 → 𝒪_F^×/U_𝔪 → (𝒪_F/λ)^× → Cl_λ(F) → Cl(F) → 1`:

- `Cl(F) = 1` — `h(ℚ(√−3)) = 1` (Eisenstein integers `ℤ[ζ₃]`, Euclidean;
  Minkowski bound `(2/π)√3 = 1.103 < 2`, so no prime to check);
- `(𝒪_F/λ)^× ≅ 𝔽₃^× = {±1}`, and the unit `−1 ∈ 𝒪_F^×` maps onto it.

Hence **`Cl_λ(F) = 1`: the ray class group is trivial.** A character `ψ`
of `G_F` that is unramified outside `λ` and tame at `λ` has conductor
dividing `λ`, so factors through `Cl_λ(F)` — **so `ψ = 1`**. Then
`ρ̄ ≅ Ind_F^ℚ 1 = 1 ⊕ ε₋₃` (dihedral case), contradicting irreducibility;
and in the cyclic case the same computation applied to `ψ·(ε₋₃-twists)` of
`G_ℚ` (restrict to `G_F`: `ψ|_{G_F}` has conductor `∣ λ`, so `ψ|_{G_F}=1`,
so `ψ ∈ {1, ε₋₃}`, values `±1 ⊆ k`, whence `ψ^σ = ψ`) contradicts
`ψ^σ ≠ ψ`. **The residual case is empty. No computation remains beyond the
two displayed bullets.** [DERIVED; the CFT input is the standard
conductor-of-tame-character ≤ λ + Artin reciprocity, e.g. Neukirch ANT VI
or Washington §3. Cross-check of the ray-class number:
`h_λ = h·|(𝒪/λ)^×|/[𝒪^× : U_λ] = 1·2/2 = 1` ✓.]

### 3.4 CFT-free variant (what one would actually formalize today)

Artin reciprocity is not in Mathlib and is itself a major FLT-project
target, so record the elementary equivalent of §3.3 (still a finite check):

1. *No unramified extensions:* any `M/F` unramified everywhere has
   `rd(M) = rd(F) = √3 = 1.732` (different-in-towers, trivial relative
   different) while `M` is totally complex of degree `≥ 4` over `ℚ`, and
   `rootDiscrBound 4 = 2.565 > 1.732` with `rootDiscrBound` strictly
   monotone (in-repo, `DiscriminantBounds.lean`). So `M = F`. [Replaces
   `Cl(F) = 1` and the Hilbert-class-field step.]
2. *Tame abelian ramification is small:* for `M/F` abelian unramified
   outside `λ`, `Gal(M/F)` equals its inertia at `λ` (by 1 applied to
   `M^{I}`), which is cyclic of order `e ∣ N(λ) − 1 = 2` (tame + abelian
   ⇒ `μ_e` in the residue field: conjugation by Frobenius on tame inertia
   is the `q`-power map, trivial iff `e ∣ q − 1`). So `M/F` is at most
   quadratic.
3. *Kummer check (the actual finite computation):* quadratic `M = F(√α)`
   unramified outside `λ` needs `α ∈ {−1, √−3, −√−3}` modulo squares
   (units mod squares `μ₆/μ₆² = {±1}`; `λ`-adic valuation 0 or 1; PID by
   step 1's class-number input). Each candidate is **wildly ramified at a
   prime above 2**: `F(√−1) = ℚ(ζ₁₂)` (disc divisible by 4);
   `F(√±√−3)` = splitting of `x⁴ ∓ 3·…` with `disc(x⁴+3) = −2⁸·3³` — in
   each case `α` is not a square in the 2-adic completion
   `F₂ = ℚ₂(ζ₃)` and the resulting quadratic is ramified at 2 (unit
   non-squares of a 2-adic field generate wildly ramified quadratics
   unless ≡ 1 mod 4𝒪). So no such `M` exists, `ψ = 1`, done — matching
   §3.3, as it must, since `Cl_λ(F) = 1`.

### 3.5 Lean cost grading (verified against Mathlib docs, 2026-08-16)

Mathlib state: `NumberField.classNumber`, `classNumber_eq_one_iff`, the
Minkowski-bound PID workflow
(`isPrincipalIdealRing_of_isPrincipal_of_lt_or_…`,
`exists_ideal_in_class_of_norm_le`) all exist —
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/ClassNumber.html;
`𝒪_{ℚ(ζ₃)} = ℤ[ζ₃]` via `Mathlib.NumberTheory.Cyclotomic.Rat`.
**Ray class groups: absent from Mathlib** (doc search 2026-08-16, no
`RayClassGroup`; the repo's `FLT/` also has zero `ClassGroup` consumers —
grep-verified). Dickson: in-repo, sorry-free (§1.4).

| Piece | Grade |
|---|---|
| `h(ℚ(√−3)) = 1` + unit surjects onto `(𝒪/λ)^×` (the finite check itself) | **S** |
| §3.4 steps 1–3 (Minkowski-unramified via in-repo `rootDiscrBound`; tame-abelian `e ∣ q−1`; three 2-adic square checks) | **M** (mostly missing relative-different/tameness glue; each step short) |
| Bridge: image classification → induced/conjugate-pair (`ρ̄ = Ind ψ`) given the Slop Dickson files | **M** |
| Alternative: build ray class groups + Artin reciprocity to use §3.3 directly | **L** (but already on the FLT project's own CFT critical path, so possibly free later) |
| **Residual branch total (CFT-free route)** | **M** |

---

## 4. Verification ledger

| Step | Status |
|---|---|
| Faber Thm A/B/6.1 (p-irregular classification, A₅ exception at p = 3), Dickson §§239–261 credit | VERIFIED-with-URL (ar5iv arXiv:1112.1999; La Matematica 2 (2023) 479–522, DOI 10.1007/s44007-023-00051-4) |
| Serre 1972 Prop. 15 exact wording | VERIFIED-as-cited (Stein BSD notes wstein.org); primary scan paywalled, NOT re-read verbatim |
| Degree-24 arithmetic incl. A₅ branch and A₄-non-lifting | DERIVED here (steps 1–5 of §1.3), elementary |
| In-repo Dickson formalization, sorry-free, with p = 3 A₅ disjunct | VERIFIED in-repo (`FLT/Slop/PGL2/FiniteSubgroups/{DicksonClassification,WildClassification}.lean`; `grep -c sorry` = 0 × 12 files) |
| `rootDiscrBound` numerics: 4.597@21, 4.637@22, 4.7696@26 vs caps 4.267/4.310/4.7622 | VERIFIED (recomputed against repo def, float64) |
| Abelian nonsplit-torus hole in the `|im| ≥ 2e₃` step (`mod_three` is `k`-irreducibility) | VERIFIED in-repo (`ModThree.lean` statement) + DERIVED |
| Raynaud 3.4.1/3.4.3–3.4.4 (`e < p − 1`, exponents ∈ {0,1} ⇒ `e₃ ∣ 8` all `k`) | VERIFIED-via-secondary (Conrad seminar L07/L08, arXiv:1109.6676); primary Numdam URL pinned, scan not OCR-read |
| Residual case unramified outside 3; `F = ℚ(√−3)` unique | DERIVED, elementary |
| Tate 1994 / Serre Œuvres III note 229.2 p. 710 (p = 3 nonexistence precedent) | VERIFIED-as-cited (arXiv:2108.07577, arXiv:2509.00635) |
| `Cl_λ(ℚ(√−3)) = 1`, λ = (√−3) | VERIFIED (exact sequence computation here: `1·2/2 = 1`) |
| Mathlib: ClassNumber API present, ray class groups absent | VERIFIED-with-URL (mathlib4_docs ClassNumber page; searches 2026-08-16) |
