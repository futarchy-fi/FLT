# Panel seat: Mazur chapter — Literature Fidelity (adversarial, web-verified)

Reviewed: `cartography/mazur-reconciled.md` (bead hub-lsb1u.2, reconciler pass 2026-08-13).
Method: web search / fetch against primary bibliographic records for every citation
touched by PQ1–PQ6. Default skeptical — unlocated ⇒ UNVERIFIED, not accepted.

## Citation spot-checks

- **Mazur 1977, "Modular curves and the Eisenstein ideal," Publ. Math. IHÉS 47, 33–186.**
  CONFIRMED real, and **Theorem 8 is exactly the torsion-classification theorem**
  (E(ℚ)_tors ∈ {15 groups, max order 16}) the map relies on throughout.
  https://www.numdam.org/item/PMIHES_1977__47__33_0/ ,
  https://link.springer.com/article/10.1007/BF02684339
  "Theorem 4 / Ch. II §9–10" (cited only in PQ5 as unverified) — I could **not** locate
  an independent secondary source quoting Thm 4's statement; genuinely UNVERIFIED,
  matches the map's own honesty flag. No refutation, but also no confirmation.

- **Mazur 1978, "Rational isogenies of prime degree," Invent. Math. 44, 129–162** (+ Goldfeld
  appendix). CONFIRMED this is the **isogeny** classification (N ≤ 19, 37, 43, 67, 163),
  distinct from the 1977 torsion theorem. **The map does NOT conflate the two** (G11
  cites both correctly, for different purposes) — checked this specifically per the
  brief and found no error. https://link.springer.com/article/10.1007/BF01390348

- **Billing–Mahler 1940**, J. London Math. Soc. s1-15, 32–43, "On Exceptional Points on
  Cubic Curves." Volume/page/year **exact match** to the map's C1/G10 citation.
  https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms/s1-15.1.32

- **Mazur–Tate 1973**, "Points of order 13 on elliptic curves," Invent. Math. 22, 41–49.
  Volume/page/year **exact match**. Method (flat-cohomology descent, J₁(13) simple,
  19-torsion of J) matches the map's D-g/C4 description.
  https://link.springer.com/article/10.1007/BF01425572

- **Kolyvagin–Logachev 1989** (Algebra i Analiz 1:5, 171–196; transl. Leningrad Math. J.
  1, 1990). CONFIRMED. Content matches the map precisely: extends Kolyvagin's Euler
  system (built on **Gross–Zagier 1986** Heegner-point machinery) to prove that
  order-of-vanishing ≤ 1 forces analytic rank = Mordell–Weil rank and Ш finite.
  The map's phrasing — "Kolyvagin–Logachev (which itself builds on Gross–Zagier
  Heegner-point machinery)" — is the **correct scoping**: it does NOT claim Gross–Zagier
  alone gives "analytic rank 0 ⇒ MW rank 0" (that would have been the scope-mismatch
  the brief warned about). No misattribution found here — the flagged risk did not
  materialize in the final reconciled text.
  https://wstein.org/papers/bib/kolyvagin-logachev-finiteness_of_the_shafarevich-tate_group_and_the_group_of_rational_points_for_some_modular_abelian_varieties.pdf

- **arXiv:2410.01466**, Best/Birkbeck/Brasca/Rodriguez Boidi/van de Velde/Yang, "A
  complete formalization of Fermat's Last Theorem for regular primes in Lean" (v1 Oct
  2024, v3 Jun 2025; published Annals of Formalized Mathematics 1, 103–132, 2025).
  CONFIRMED: covers **both cases** of FLT for **all regular primes** (Kummer's lemma via
  Hilbert 90–94), not just a partial/first-case result. Since 5, 7, 11, 13 are all
  regular (first irregular prime is 37), this **substantiates** the reconciler's D-h
  observation that re-basing could go as far as p ≥ 17-regular-excluded, deleting
  C1–C4 entirely — the map's own claim is *conservative*, not overreaching.
  https://arxiv.org/abs/2410.01466

- **Michaud-Jacobs arXiv:2209.03153**, "Mazur's isogeny theorem" — confirmed real,
  expository overview of the 1978 isogeny paper, consistent with G11's citation.
  https://arxiv.org/abs/2209.03153

- **Merel 1996**, Invent. Math. 124, 437–449 — bibliographic form matches standard
  citation; winding-quotient construction and its role replacing the Eisenstein
  quotient in Kamienny's criterion is correctly described (D6b).

## The refutation: C5 / PQ3 (ℓ = 17, 19 "classical via Ogg/Kubert")

**REFUTED.** X₁(17) has genus 5 and X₁(19) has genus 7 (vs. X₁(11) genus 1,
X₁(13) genus 2). Multiple independent sources confirm the pre-Mazur classical
descent techniques (Billing–Mahler on the genus-1 X₁(11); Mazur–Tate's flat-cohomology
descent on the genus-2 J₁(13)) did **not** extend to N = 17, 19 — these higher-genus
cases were resolved *only* as instances of Mazur's general 1977 Eisenstein-ideal
theorem, not by any earlier ad hoc classical method. There is no Ogg/Kubert classical
result eliminating rational 17- or 19-torsion prior to Mazur 1977. C5's "possible
cheapening of the D-core's lower edge" therefore does not exist as claimed — ℓ = 17, 19
are squarely D-core (Part D) primes, not classical Part-C primes. P1's attribution
(already self-flagged "unverified" in the map) should be struck, not merely left as
low-confidence.
Sources: genus-5/7 facts and classical-history summary cross-checked against
Ogg 1971 (Invent. Math. 12, 105–111), the Mazur–Tate paper's own framing, and
secondary surveys (Ogg's Torsion Conjecture: Fifty Years Later,
https://arxiv.org/pdf/2307.04752 ; Dembner, "Torsion on Elliptic Curves and Mazur's
Theorem," https://math.uchicago.edu/~may/REU2019/REUPapers/Dembner.pdf).

## PQ verdicts (literature-fidelity lens only; PQ7 out of scope)

- **PQ1** (D8 endgame vs Mazur 1977 Thm 8 / Snowden L20–25): **UNVERIFIED** — Thm 8's
  exact statement (torsion classification) is confirmed, but the precise char-2/3
  special-fibre counting sub-derivation used in D8 requires a page-level read of a
  150-page paper I could not complete; no error found, none ruled out.
- **PQ2** (D6 fork bibliography — Eisenstein vs winding/KL/GZ): **VERIFIED** — all
  citations check out with correct years and correct scope; the map's careful
  "builds on" phrasing avoids the Gross–Zagier scope-mismatch the brief flagged as a
  risk.
- **PQ3** (ℓ = 17, 19 classical via Ogg/Kubert, C5): **REFUTED** — genus 5/7, not
  classically resolved pre-1977; see above. Worst finding of this review.
- **PQ4** (regular-prime re-basing ceiling): **VERIFIED** — arXiv:2410.01466 formalizes
  FLT for all regular primes unconditionally (both cases), confirming 5/7/11/13 are
  all in scope and the reconciler's "push to p ≥ 17-regular-excluded" reading is sound
  or even conservative.
- **PQ5** (unverified-citation punch list): **PARTIALLY VERIFIED** — Billing–Mahler and
  Mazur–Tate citations confirmed exact (volume/page/year); Serre Duke 1987 §4.1 Prop 6,
  Silverman AEC VII.3.1, Katz 1980 Appendix, and the X₁(2,10)/X₁(2,14)/X₁(11)=121b1
  conductor claims remain **UNVERIFIED** (not located with confidence in the time
  available) — correctly left open by the map, no further resolution obtained.
- **PQ6** (integral-model sizing, Katz–Mazur vs ad hoc): this is a formalization-scoping
  question, not a checkable literature claim — **UNVERIFIED / not a citation to check**;
  no literature error found because none was assertable.

## Overall

**SOUND-with-repairs.** The reconciled map's core bibliography (Mazur 1977/1978,
Billing–Mahler, Mazur–Tate, Kolyvagin–Logachev, Merel, arXiv:2410.01466) checks out on
every point tested, including the two traps the brief specifically set (1977/1978
torsion-vs-isogeny conflation: avoided; Gross–Zagier scope mismatch: avoided). The one
concrete defect is **C5 (ℓ = 17, 19 "classical")**, which should be deleted from the
Part-C/PQ3 table rather than left as "low confidence" — it is not a gap in verification,
it is a checked-and-wrong historical claim. This does not affect the load-bearing D-core
argument (D1–D9), which never relied on C5; it only affects milestone-ordering language
in §4/§5 that should stop citing C5 as a live cheapening option.
