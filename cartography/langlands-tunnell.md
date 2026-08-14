# Chapter map: Langlands–Tunnell — modularity of mod-3 representations

Bead: hub-lsb1u.3 (P1 cartography, first pass)
Repo snapshot: `main` @ e99f167 ("chore: remove the Update Dependencies workflow (#1164)"), 2026-08-13.
Cartography only — no proving, no Lean.

---

## 0. Headline finding (read this first)

**The FLT-project route does not use Langlands–Tunnell at all, and says so explicitly.**

`FLT/Assumptions/Odlyzko.lean:30-41`:

> "The original proof by Wiles and Taylor-Wiles of FLT contains a crucial step
> where they "switch to the prime 3", and apply the Langlands--Tunnell theorem
> to deduce that the 3-torsion in an elliptic curve over ℚ, if irreducible,
> is modular. In the argument we are formalizing, we switch to 3 at a different
> point. The advantage of this is that it avoids the Langlands-Tunnell theorem
> (which needs non-Galois cubic cyclic base change); the analysis we need is
> easier. We switch to 3 only after we have constructed a compatible family
> of Galois representations with conductor 2 from the Frey curve (using hard
> modularity lifting theorems), and we use this bound below to demonstrate
> that such a family cannot exist. The argument involves a careful analysis of
> the 3-torsion in the 3-adic specialization of the family; it is analogous to
> Fontaine's proof that there is no nontrivial abelian variety over ℤ."

These are the **only** occurrences of "Tunnell" in the entire repo (LaTeX + Lean).
The blueprint's residual-modularity input is instead **potential modularity via
Moret–Bailly + automorphic induction + a modularity lifting theorem**
(`blueprint/src/chapter/ch04overview.tex:27-34, 102-108`), with the mod-3 switch
performed at the *end* via Odlyzko bounds and a Fontaine-style non-existence
argument (`ch04overview.tex:110-119`; axiom `Odlyzko_statement` at
`FLT/Assumptions/Odlyzko.lean:58-59`).

What the project *does* assume from the Langlands corpus is **cyclic (Galois,
prime-degree) base change for GL(2)** — that is bead hub-lsb1u.5's chapter, not
this one:

- `blueprint/src/chapter/ch01introduction.tex:50-52` — "we will assume Langlands' cyclic base change theorem for $\GL_2$"
- `blueprint/src/chapter/ch04overview.tex:86-88` — Skinner–Wiles trick "needs cyclic base change for $\GL(2)$ and also a characterisation of the image of the base change construction; this seems to need a multiplicity one result, which ... will need Jacquet--Langlands as well."
- `blueprint/src/chapter/chtopbestiary.tex:213-215` — "we need cyclic base change plus classification of image, all for totally definite quaternion algebras, and we need automorphic induction from $\GL_1(K)$ to $\GL_2(F)$"
- `FLT/Assumptions/README.md:55-60` — planned assumptions: automorphic induction GL_1→GL_2, cyclic base change for GL_2 + classification of image, Jacquet–Langlands.
- `FLT/Assumptions/KnownIn1980s.lean:39` — the `knownin1980s` axiom's documented scope includes "Langlands on cyclic base change".

The Tunnell-specific ingredient — base change through the **non-normal cubic**
subfield of an S₄-extension — appears nowhere in the repo's plan. This chapter is
therefore a **contingency map**, not a live dependency of the current route.

---

## 1. What FLT needs

### 1a. What the classical (Wiles 1995) route needs

**Langlands–Tunnell, as used by Wiles (Ch. 5 of [Wiles1995]):**

> Let ρ̄ : G_ℚ → GL₂(𝔽₃) be continuous, odd, and irreducible. Then ρ̄ is modular:
> there is a weight-1 (hence, after multiplying by a suitable Eisenstein series
> and using a mod-3 congruence, weight-2) newform f and a prime λ | 3 of its
> coefficient field with ρ̄_{f,λ} ≅ ρ̄ ⊗ (twist).

Mechanism: the standard faithful 2-dimensional complex representation
Ψ : GL₂(𝔽₃) ↪ GL₂(ℤ[√−2]) ⊂ GL₂(ℂ) turns ρ̄ into an odd 2-dimensional **Artin**
representation with **solvable** image (|GL₂(𝔽₃)| = 48; projective image ⊆ S₄).
Langlands (1980) proves such Artin representations automorphic in the dihedral
and tetrahedral (proj. image A₄) cases; Tunnell (1981) settles the octahedral
(proj. image S₄) case. The resulting automorphic representation corresponds to a
weight-1 form; reduction mod (a prime above) 3 recovers ρ̄ up to twist.

### 1b. Weakest sufficient version (classical route, Frey curve at 3)

Full Langlands–Tunnell (all odd 2-dim solvable-image Artin reps over all number
fields) is **not** needed. Sufficient:

- Base field ℚ only (Wiles applies it over ℚ; the potential-modularity variants
  apply it after restriction to a totally real F, so "ℚ and totally real F" for
  the 21st-century variants — Taylor's Remarks on a paper of Kisin, Kisin's
  Fontaine–Laffaille paper both still route residual modularity at 3 through
  Langlands–Tunnell over the relevant totally real field).
- Image exactly inside GL₂(𝔽₃) via the fixed twist Ψ — so only projective images
  ⊆ S₄ arise, and only three cases are live:
  - **reducible**: not needed (Wiles handles ρ̄₃ reducible via the 3–5 switch);
  - **dihedral**: automorphic induction from GL₁ (CM/Hecke theta series — 1930s
    technology, and already on the repo's assumption list independently);
  - **A₄ (tetrahedral)**: Langlands 1980;
  - **S₄ (octahedral)**: Tunnell 1981. This is the only part where the
    non-normal cubic base change is required, and the only content that is
    irreducibly "this chapter's".
- Only ℓ = 3 matters: one fixed embedding GL₂(𝔽₃) → GL₂(ℂ) and one fixed
  congruence (E₁ ≡ 1 mod 3) for the weight-1 → weight-2 step.

So the weakest classical statement is: **"every continuous odd irreducible
ρ̄ : G_F → GL₂(𝔽₃) (F = ℚ or the specific totally real fields arising) with
projective image A₄ or S₄ is modular"** — plus the (independently-needed)
dihedral case.

### 1c. What the *repo's* route needs from this chapter

**Nothing.** The route replaces residual-modularity-at-3 by: potential
modularity of ρ̄_ℓ (ℓ ≥ 5) via Moret–Bailly with an auxiliary prime whose mod-p
representation is *induced from a character* (dihedral — converse
theorems/automorphic induction, no Tunnell), then Khare–Wintenberger + the
compatible-family/Brauer trick of [BLGGT], then a mod-3 **non-existence**
argument (Fontaine-style, powered by the Odlyzko bound axiom). See
`ch04overview.tex:102-119` and `FLT/Assumptions/Odlyzko.lean`.

---

## 2. Statement inventory

Sizes: S ≤ 1 wk-person, M ≤ 1 mo, L ≤ 6 mo, XL > 6 mo (formalization effort,
assuming hub-lsb1u.4/.5 chapters done). "(unverified)" marks
citation numbers not checked against the physical text.

**LT-1. The twist Ψ : GL₂(𝔽₃) ↪ GL₂(ℤ[√−2]).** Explicit faithful 2-dim complex
representation of GL₂(𝔽₃); Ψ ⊗ 𝔽₃ ≅ id up to twist. Concrete matrices are
written down in [Wiles1995, Ch. 5] (unverified page). **S.**

**LT-2. Image classification.** A finite subgroup of GL₂(ℂ) (equivalently
PGL₂(ℂ)) with irreducible action is cyclic-projectively: dihedral, A₄, S₄, or
A₅; solvable excludes A₅. For subgroups of GL₂(𝔽₃): projective image ⊆ PGL₂(𝔽₃)
≅ S₄. Classical (Klein/Dickson); cf. [Serre1972 §2] (unverified). **S–M.**

**LT-3. Dihedral case: automorphic induction GL₁(K) → GL₂(F).** Modularity of
induced-from-character representations (Hecke, Maass; adelically
Jacquet–Langlands [JL1970 §12] (unverified)). **EXTERNAL EDGE** — this exact
statement is already on the repo's own assumption list
(`FLT/Assumptions/README.md:55`, `chtopbestiary.tex:214-215`) and belongs to the
cyclic-base-change/automorphic-induction chapter (hub-lsb1u.5). **(L there.)**

**LT-4. Cyclic base change for GL(2), prime degree, with characterization of
image.** Langlands, *Base Change for GL(2)*, Ann. of Math. Studies 96, 1980
(main theorems; trace-formula proof). **EXTERNAL EDGE → hub-lsb1u.5** (that
chapter's core node). **(XL there.)**

**LT-5. Tetrahedral case (Langlands).** An odd 2-dim Artin representation of
G_ℚ (or G_F, F totally real) with projective image A₄ is automorphic (cuspidal).
Proof: base change through the cyclic cubic layer of the A₄-field + Gelbart–
Jacquet lifting + descent. [Langlands1980, §3 / "Proofs of theorems A and B"]
(unverified section). **L** (given LT-4 and LT-8 as inputs).

**LT-6. Octahedral case (Tunnell). THE chapter-defining node.** An odd (in
fact, any, over a number field) 2-dim Artin representation with projective
image S₄ is automorphic. Proof: pass to the quadratic subfield fixed by A₄
inside the S₄-field (tetrahedral there, so automorphic by LT-5), then descend
through the **non-normal cubic** subextension using base change for the cyclic
cubic over the quadratic, converse-theorem/L-function arguments, and a clever
trichotomy. [Tunnell1981] = J. Tunnell, "Artin's conjecture for representations
of octahedral type", Bull. AMS (N.S.) 5 (1981), 173–175. Three pages of prose,
but standing on the full weight of LT-4, LT-8, LT-9. **L** on top of its
inputs; **XL** if its inputs are charged to it.

**LT-7. Gelbart–Jacquet symmetric-square lifting GL(2) → GL(3).** Needed
inside LT-5/LT-6's proofs. [GJ1978] = Gelbart–Jacquet, Ann. Sci. ENS 11 (1978)
(unverified). Trace-formula/theta machinery for GL(3). **XL.** (Arguably its own
external chapter if this route were ever activated; no existing bead.)

**LT-8. Converse theorem for GL(2) (Weil/Jacquet–Langlands §14).** Analytic
continuation + functional equations of enough twists ⇒ automorphic. Used in
LT-3, LT-6. [JL1970 Thm 14.2] (unverified). Partial overlap with hub-lsb1u.4's
analytic toolbox; provisionally **internal here, L**.

**LT-9. Artin ⇒ weight-1 form dictionary.** An odd cuspidal automorphic rep of
GL₂(𝔸_ℚ) with the Galois-type infinity component corresponds to a holomorphic
weight-1 newform whose Artin representation is the given one (Deligne–Serre
[DS1974] gives the harder converse; the direction needed here is the easier
one). **M.**

**LT-10. Weight 1 → weight 2 mod 3, and mod-3 glue.** Multiply the weight-1
form by the Eisenstein series E₁(χ₋₃) ≡ 1 (mod 3) to get a weight-2 form
congruent to it; deduce ρ̄_{f,λ} ≅ ρ̄ ⊗ twist, i.e. ρ̄ is modular in the sense
the deformation theory needs. [Wiles1995 Ch. 5] (unverified). **M.**

Chapter-proper nodes: LT-1, LT-2, LT-5, LT-6, LT-8, LT-9, LT-10 (7 nodes).
External: LT-3, LT-4 (→ hub-lsb1u.5), plus LT-7 (unassigned XL), plus
Jacquet–Langlands correspondence proper (→ hub-lsb1u.4, used wherever
"modular" means quaternionic as in this repo, `chtopbestiary.tex:213`).

---

## 3. Dependency edges

Internal:
- LT-6 ← LT-5 (octahedral reduces to tetrahedral over the quadratic subfield)
- LT-5 ← LT-2, LT-8; LT-6 ← LT-2, LT-8
- LT-9 ← LT-5/LT-6 output (the automorphic rep)
- LT-10 ← LT-9, LT-1 (twist bookkeeping)
- Chapter output ("ρ̄₃ modular") ← LT-10; consumed by the *classical* modularity
  lifting step, not by anything in this repo.

External (chapter bead named):
- LT-5, LT-6 ← **cyclic base change for GL(2)** [LT-4] → bead hub-lsb1u.5
- LT-3 (dihedral) ← **automorphic induction** → bead hub-lsb1u.5
- LT-5, LT-6 ← **Gelbart–Jacquet Sym²** [LT-7] → no existing bead (flag)
- "modular" in the repo's quaternionic sense ← **Jacquet–Langlands + mult. one**
  → bead hub-lsb1u.4 (`ch04overview.tex:86-88`, `chtopbestiary.tex:213`)
- LT-10's congruence ← standard modular-forms theory (Mathlib `ModularForm`
  namespace + q-expansion work; no bead).

---

## 4. Mathlib anchors (web/repo-checked 2026-08-13)

- **Automorphic forms / representations: ABSENT from Mathlib4.** Only classical
  modular forms exist: `Mathlib.NumberTheory.ModularForms.*` (`ModularForm`,
  `CuspForm`, `SlashInvariantForm`, Eisenstein series, Petersson). The only
  Lean "automorphic form" is the FLT repo's own
  `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm`
  (`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`, plus
  `FiniteDimensional.lean`, `InnerProduct.lean`, Hecke operators) — quaternionic
  weight-2 only; nothing for GL₂(𝔸) proper, nothing analytic. **Status:
  absent (Mathlib) / partial-bespoke (FLT repo).**
- **GL₂(𝔽₃) representation theory:** Mathlib has general finite-group
  representation theory (`Mathlib.RepresentationTheory.*`: `Rep k G`,
  Maschke, characters, `FDRep`) and `Matrix.GeneralLinearGroup` /
  `Matrix.SpecialLinearGroup`; no explicit character table or the Ψ embedding
  for GL₂(𝔽₃). LT-1/LT-2 would be from-scratch but small. **Status: partial.**
- **Weil representation: ABSENT.** No Weil/oscillator representation, no
  metaplectic group, no theta correspondence in Mathlib4 (search of docs +
  namespaces finds nothing; only classical Jacobi-theta material under
  `Mathlib.Analysis.SpecialFunctions.JacobiTheta` and modular-forms files).
  This blocks any faithful formalization of Gelbart–Jacquet (LT-7) and of the
  theta-series side of LT-3.
- **Artin L-functions / converse theorems: ABSENT.** Mathlib has `LSeries`,
  Dirichlet L-functions, functional equation machinery for degree 1
  (`Mathlib.NumberTheory.LSeries.*`); nothing degree-2, no converse theorem
  (LT-8 from scratch).
- **Trace formula: ABSENT** (relevant to LT-4/LT-7, i.e. the external XL
  nodes).

---

## 5. Route risk

- **This chapter is very likely moot.** The repo route bypasses
  Langlands–Tunnell by design (`FLT/Assumptions/Odlyzko.lean:30-41`),
  trading it for the Odlyzko-bound axiom + a Fontaine-style mod-3
  non-existence argument after Khare–Wintenberger. **Campaign-level
  recommendation: downgrade bead hub-lsb1u.3 to contingency status**; the live
  siblings are hub-lsb1u.5 (cyclic base change — Galois cases only, no
  non-normal cubic needed) and hub-lsb1u.4 (Jacquet–Langlands).
- **Size verdict: yes, if activated it would be the largest deferred-gap
  item** — but mostly by transitivity. Chapter-proper content (LT-1,2,5,6,8,
  9,10) is ~2L + 2M + 2S ≈ comparable to the JL chapter alone; however its
  closure drags in full trace-formula base change (XL, shared with
  hub-lsb1u.5) *plus* Gelbart–Jacquet GL(3) lifting (XL, **charged to no
  existing bead** — flag for the hub if this route is ever revived). Total
  closure ≳ any other single chapter. The bypass is precisely what deletes the
  non-shared XL (LT-7) and the non-normal-cubic strengthening of base change.
- **Cyclic base change does not disappear.** Even on the bypass route, the
  Skinner–Wiles minimality trick needs cyclic base change + image
  characterization + multiplicity one + JL (`ch04overview.tex:86-88`,
  `chtopbestiary.tex:213-215`, `FLT/Assumptions/README.md:52-60`). Risk of
  double-counting between beads .3 and .5 if this chapter is kept live.
- **Residual contingency:** if the Odlyzko/Fontaine mod-3 endgame stalls
  (its axiom `Odlyzko_statement` is one of only two formalized assumptions,
  issue #458), the classical fallbacks are (a) Langlands–Tunnell + 3-5 switch
  (this chapter, XL closure), or (b) other residual-modularity inputs (e.g.
  p = 5 switching still needs *some* residually-modular anchor, classically
  supplied at 3 — so (b) does not obviously avoid (a)). Keep this map on file.
- **Everything here rests on `knownin1980s`-era assumptions for now**
  (`FLT/Assumptions/KnownIn1980s.lean:39` names Langlands' cyclic base change
  explicitly in the axiom's charter), so no Lean statement of any node exists
  yet; first formalizable target on the live route is the modularity lifting
  theorem (`ch04overview.tex:70-84`, marked `\notready`), not anything
  Tunnell-shaped.

---

## References

- R. P. Langlands, *Base Change for GL(2)*, Annals of Math. Studies 96,
  Princeton, 1980.
- J. Tunnell, "Artin's conjecture for representations of octahedral type",
  Bull. AMS (N.S.) 5 (1981), 173–175.
- S. Gelbart, H. Jacquet, "A relation between automorphic representations of
  GL(2) and GL(3)", Ann. Sci. ENS 11 (1978). (unverified pages)
- H. Jacquet, R. Langlands, *Automorphic Forms on GL(2)*, LNM 114, 1970.
- P. Deligne, J.-P. Serre, "Formes modulaires de poids 1", Ann. Sci. ENS 7
  (1974).
- A. Wiles, "Modular elliptic curves and Fermat's Last Theorem", Ann. of Math.
  141 (1995), Ch. 5.
- [BLGGT] Barnet-Lamb–Gee–Geraghty–Taylor, "Potential automorphy and change of
  weight" (compatible-family/Brauer trick, as cited `ch04overview.tex:112`).
