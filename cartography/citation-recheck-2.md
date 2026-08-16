# Citation recheck 2 — panel-repair execution (JL repair 3, CFT repair 4)

P1 panel-repair pass, 2026-08-16. Sources: `panel/jl-adjudication.md` repair 3,
`panel/jl-literature.md`, `panel/cft-adjudication.md` repair 4,
`panel/cft-literature.md` §5. All verdicts below are against primary texts
fetched this session unless marked otherwise. LOCAL tree only.

## 1. JL weight-2 transfer citation (replaces bare "Shimizu 1972")

**Verdict: Jacquet–Langlands 1970 itself wins as primary anchor — Thm 14.4 +
Thm 16.1 — supplemented by Martin 2020 Thm 1.1 for the classical-forms/level-
explicit statement. The weight>2 restriction is an artifact of Shimizu's
basis-problem application, not of the correspondence.**

Verified against the typeset primary text of JL, *Automorphic Forms on GL(2)*,
LNM 114 (1970), IAS electronic edition:
https://publications.ias.edu/sites/default/files/automorphic-forms-on-gl2_rpl_9.pdf

- **JL 1970, Theorem 14.4** (Ch. III §14, p. 248 of typeset ed.). Verbatim: "If
  π′ is a constituent of A′ and π′_v is infinite-dimensional at any place where
  M′ splits then π is a constituent of A₀." One line: forward transfer
  D× → GL₂-cuspidal with NO weight/archimedean restriction — the
  infinite-dimensionality hypothesis binds only at SPLIT places, so the
  finite-dimensional (trivial-on-SU(2)) component at totally definite infinite
  places — i.e. parallel weight 2 / trivial infinitesimal character — is
  covered. The archimedean local map π_v(π′_v) sends Symⁿ ↦ weight-(n+2)
  discrete series (n = 0 gives weight 2; cf. Conrad JL-seminar L20 §1.3,
  http://virtualmath1.stanford.edu/~conrad/JLseminar/Notes/L20.pdf).
- **JL 1970, Theorem 16.1** (Ch. III §16, p. 262). One line: converse/image
  characterization — a cuspidal π of GL₂ that is special or absolutely cuspidal
  (= discrete series) at every v ∈ S comes from D×; again weight-blind.
  **Ledger caveat (new finding, load-bearing):** JL themselves write in §16
  that their trace-formula argument is "merely a formal argument so that the
  theorem must remain, for the moment, conjectural" — the analytic details were
  completed in **Gelbart–Jacquet, "Forms of GL(2) from the analytic point of
  view," Proc. Sympos. Pure Math. 33 (1979) part 1, 213–251, §8** (the source
  Conrad's notes follow). Any ledger citing JL §16 for the GL₂→D direction
  should co-cite Gelbart–Jacquet 1979 §8.
- **Shimizu 1972** (J. Math. Soc. Japan 24, 638–683,
  https://www.jstage.jst.go.jp/article/jmath1948/24/4/24_4_638/_article),
  primary text extracted: his stated purpose is "another proof of
  Jacquet-Langlands [5, Th. 14.4]"; his **Theorem 1** (§5, no. 12) proves the
  correspondence "under a weaker condition that π is not one-dimensional" —
  weight-blind; the **weight > 2 at each infinite place** condition attaches to
  his **Theorem 2** (§6, no. 5), the holomorphic/basis-problem application
  generalizing Eichler. So the panels' weight-2 gap is real for Shimizu-as-
  classical-statement, and Shimizu remains a fine citation for the abstract
  correspondence — but not for the weight-2 classical transfer.
- **Martin, "The basis problem revisited," Trans. Amer. Math. Soc. 373 (2020)
  4523–4559** (https://arxiv.org/abs/1804.04234), full text verified: quaternionic
  weight k ≥ 0 corresponds to Hilbert weight k+2, so **k = 0 = parallel weight 2
  is included; his Theorem 1.1 carries no weight hypothesis**. Theorem 1.1: a
  Hecke-module homomorphism JL : S_k(O) → S_{k+2}(N) for special/Eichler orders
  O of ARBITRARY level N over any totally real F, injective (an isomorphism onto
  ⊕_d S^{d-new}_{k+2}(dM)) when v_p(N) is odd for all p | D; Theorem 1.2 +
  Corollary 1.3 solve the basis problem; his §5.2 handles the weight-2-specific
  caveat (1-dimensional/norm-factoring reps ↔ weight-2 Eisenstein series) —
  exactly the PQ6 exclusion clause. Best modern anchor at our U₁(S)-type level
  structure.
- **"Hida 1981 (Iwanami/AJM basis-problem)" — REFUTED as a candidate.** Hida's
  1981 papers (AJM 103, 727–776 = Shimura-curve/CM factors; Invent. Math. 63 and
  64 = congruence papers) are not basis-problem papers. The actual Hida anchor is
  **Hida, "The integral basis problem of Eichler," IMRN 2005** (open copy:
  https://escholarship.org/content/qt7q7205p0/qt7q7205p0_noSplash_969e70eaf200c0264779fedf12e1f199.pdf),
  whose **Theorem 2.1 (Eichler, Jacquet–Langlands)** states the weight-2
  isomorphism S(ℂ) ≅ S₂(p;ℂ) as Hecke modules for totally definite B over
  totally real F, and Corollary 2.2 gives the integral refinement — useful as a
  weight-2-specific supplementary citation, under the corrected year/venue.

**Recommended ledger line:** JL 1970 Thm 14.4 + Thm 16.1 (image; analytic
completion Gelbart–Jacquet 1979 §8) for the representation-theoretic transfer,
Martin 2020 Thm 1.1 for the weight-2 classical statement at explicit level;
Shimizu 1972 Thm 1 optional (correspondence only — his Thm 2 is weight > 2);
Hida cited as IMRN 2005, not 1981.

## 2. Coefficient bridge (ℂ ↔ ℚ̄_p eigensystem transfer, JL node N4)

**Both anchors confirmed to exist; the Duke 1978 paper (not the 1971 book) is
the right Shimura reference for the Hilbert case.**

- **Shimura, "The special values of the zeta functions associated with Hilbert
  modular forms," Duke Math. J. 45 (1978) no. 3, 637–679**, doi
  10.1215/S0012-7094-78-04529-5,
  https://projecteuclid.org/journals/duke-mathematical-journal/volume-45/issue-3/The-special-values-of-the-zeta-functions-associated-with-Hilbert/10.1215/S0012-7094-78-04529-5.short
  (paywalled full text; existence + pinpoints verified via Project Euclid and
  via Sakugawa–Sugiyama's own citation). Pinpoints: **Proposition 2.2** —
  Hecke eigenvalues of Hilbert modular forms of PARALLEL weight are algebraic
  integers (proved by constructing a basis of M_k(𝔫,χ) from Siegel modular
  forms with integral coefficients); **Proposition 2.8** — the Fourier
  coefficients generate a totally real or CM number field ℚ(f) (weights
  congruent mod 2). Note the published **Corrections, Duke Math. J. 48 (1981)
  697**
  (https://projecteuclid.org/journals/duke-mathematical-journal/volume-48/issue-3/Corrections-to-The-special-values-of-the-zeta-functions-associated/10.1215/S0012-7094-81-04838-9.short)
  should ride along in the ledger. The 1971 Princeton book (*Introduction to
  the Arithmetic Theory of Automorphic Functions*) covers only F = ℚ
  (rationality, Thm 3.48/3.52) — insufficient for the Hilbert route; cite Duke
  1978.
- **Sakugawa–Sugiyama, "Integrality of Hecke eigenvalues and the growth of
  Hecke fields," arXiv:2401.11716** (v1 Jan 2024, v2 May 2026;
  https://arxiv.org/abs/2401.11716) — verified to exist; **Theorem 1.1**:
  Hecke eigenvalues of arbitrary Hilbert (and Siegel) modular forms — any
  weight, including non-parallel and non-paritious — are algebraic integers,
  by a method independent of cohomologicality and Galois representations.
  Verified (HTML v2) that it cites Shimura Duke 1978 as [58, Proposition 2.2]
  for the parallel-weight case: "if 𝐤 is parallel, then Shimura proved in
  [58, Proposition 2.2] that those Hecke eigenvalues are algebraic integers."
  Confirms the panel seat's anchor and the Shimura-not-Waldspurger ruling (PQ7).

## 3. CFT NSW/Milne citation remainder

Grep surface: `cartography/cft-reconciled.md`, `cartography/cft.md`,
`cartography-b/cft.md`. Already-verified list carried across from the PT panel
(8.7.9, 8.6.7, 8.6.10, 8.7.8, 7.1.4, 7.1.8, 7.2.6, 7.3.1) excluded. Grep
result: the ONLY NSW pinpoint outside that list in these three files is
**NSW 8.1** (cft-reconciled.md:116 and :160); there are **no pinpoint Milne
citations** in any of the three files (only generic "Neukirch/Milne route"
phrasing, cft.md:5,89,145 — nothing to verify). Two Serre *Galois Cohomology*
pinpoints in `cartography-b/cft.md` were swept in as the remaining
non-NSW-numbered pinpoints. Verified against the NSW electronic edition v2.3
(free PDF, https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/), text extracted
this session.

| Citation (location) | Claimed content | Verdict |
|---|---|---|
| NSW 8.1 (cft-reconciled.md:116, node 8/D2) | "CFT export: global reciprocity / Σ inv_v = 0 (class-formation cut)" | **VERIFIED** — §8.1 contains Thm (8.1.17): exact sequence 0 → Br(k) → ⊕_p Br(k_p) → ℚ/ℤ → 0 with inv_k = Σ inv_{k_p} (verbatim), Thm (8.1.22): C is a formation module w.r.t. the inv maps, and Thm (8.1.23): global reciprocity C_k/N_{K\|k}C_K ≅ G(K\|k)^ab |
| NSW 8.1 (cft-reconciled.md:160) | "the packaged class formation '(G_S, C_S)'" | **REFUTED-with-correction** — the (G_S, C_S) class-formation statement is **NSW Proposition (8.3.9)** ("The pair (G_S,C_S) is a class formation", with H^i(G_S,C_S) computed), in §8.3, not §8.1; §8.1 packages the full-idele-class formation (G_k, C) (8.1.22). Correct the pinpoint to NSW 8.3.9 (or "NSW 8.1 + 8.3.9") |
| Serre, *Galois Cohomology* §5.2 Prop 14 (cartography-b/cft.md:16, `local_galois_coh_finite`) | finiteness of local Galois cohomology of finite modules | **VERIFIED** (secondary-but-exact) — Ch. II §5 "p-adic fields", §5.2 "Cohomology of finite G_k-modules"; Prop 14 = H^n(k,A) finite for finite A; quoted with this exact number+content by Chernousov–Rapinchuk–Rapinchuk, arXiv:1602.04517 ("generalizes [Serre, Ch. II, §5, Proposition 14]") |
| Serre, *Galois Cohomology* II.5 (cartography-b/cft.md:73, H²(G_K,μ_n) ≅ ℤ/n) | Brauer-group invariant map lives in Ch. II §5 | **VERIFIED** at section granularity — Ch. II §5 ("p-adic fields", §5.1 summary incl. Br(k) ≅ ℚ/ℤ); independently confirmed by the CFT literature seat this wave |
| Milne (ADT/CFT) pinpoints | — | **none exist** in the three files; no action |

**Remainder tally: 3 VERIFIED / 1 REFUTED-with-correction (NSW 8.1 → 8.3.9 for
(G_S,C_S)) / 0 UNVERIFIED-paywalled.** (Shimura Duke 1978 full text in §2 is
the only paywalled item this pass, and its pinpoints were verified through
Sakugawa–Sugiyama's direct quotation.)
