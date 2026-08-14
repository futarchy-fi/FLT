# Panel verdict — Poitou–Tate reconciled map, LITERATURE FIDELITY lens

Reviewed: `origin/cartography/pt-reconciled:cartography/pt-reconciled.md` (bead hub-lsb1u.7.4).
Primary sources fetched and text-extracted directly (not taken from search snippets):
NSW 2nd ed. corr. 2nd printing PDF (mathi.uni-heidelberg.de/~schmidt/NSW2e/NSW2.3.pdf, v2.3
May 2020) + errata (errata-nsw2e.pdf); Wiles, *Modular Elliptic Curves and Fermat's Last
Theorem*, Annals 141 (1995) (wstein.org copy); Milne, *Arithmetic Duality Theorems* 2nd ed.
(jmilne.org/math/Books/ADTnot.pdf); Darmon–Diamond–Taylor survey (math.mcgill.ca/darmon).

## Per-claim verdicts

1. **NSW 8.7.9 = Greenberg–Wiles order formula, attributed to Wiles.** CONFIRMED verbatim.
   Text reads "The following theorem is due to A. WILES," module A finite, order prime to
   char(k), formula `#H¹_L(k,A)/#H¹_{L^D}(k,A') = #H⁰(k,A)/#H⁰(k,A') · Π_p #Lp/#H⁰(kp,A)` —
   matches the map's §5 item 6 axiom text exactly, including the A' = Hom(A,μ) convention.

2. **NSW 8.6.7 = Sha-duality, 8.6.10 = nine-term sequence.** CONFIRMED. 8.6.7 is literally
   titled "Theorem (Poitou-Tate Duality)" — the perfect pairing Ш¹(A₀)×Ш²(A)→Q/Z; 8.6.10 is
   "Long Exact Sequence of Poitou-Tate," explicitly a sequence "of topological groups" with
   each term labeled finite/compact/discrete — matches the map's §2.3 characterization
   ("strict morphisms, restricted-product topology, Pontryagin duals") term for term. Node 14
   (Selmer/dual conditions, NSW 8.7.8) also verified verbatim.

3. **Wiles Prop 1.6 matches the NSW-shape order formula the map attributes to it.**
   PARTIALLY REFUTED — shape mismatch, not a wrong citation but an imprecise one. Wiles's
   actual Prop 1.6 (p.472) is stated over **Q only**, for X of **p-power order**, and splits
   the archimedean place out as a *separate* factor h∞ = #H⁰(R,X*)#H⁰(Q,X)/#H⁰(Q,X*),
   multiplied against Π_{q∈Σ} hq over **finite** primes only — not the single uniform
   product over all places (with Ĥ⁰ folded in) that NSW 8.7.9 and the map's axiom use. The
   uniform-product shape the map states verbatim is **DDT Theorem 2.18** (p.60 of the survey),
   which explicitly re-derives Wiles's result in NSW-compatible form for general finite M
   over Q. The map's own refs list ("NSW 8.7.9; Wiles Prop 1.6; DDT §2") already includes DDT,
   so this is defensible as a package — but citing "Wiles Prop 1.6" as if it independently
   yields the stated formula-shape overclaims; the exact displayed formula is traceable to
   NSW 8.7.9 / DDT 2.18, not to Wiles's paper verbatim.

4. **Milne ADT cross-references.** CONFIRMED with one added finding: Milne I.4.10 (p.57,
   2nd ed.) is confirmed to bundle *both* the Sha-pairing and the nine-term sequence in one
   theorem (parts a/b), consistent with the map citing it for node 11. Node 7/8/12 refs
   (Milne I.2.3, I.2.8, I.5.1) are consistent with Wiles's own proof of Prop 1.6, which cites
   "[Mi2, Cor. 2.3 and Th. 5.1]" for local duality and global Euler characteristics — good
   independent corroboration. **However**, Wiles's proof of Prop 1.6 itself cites **Milne
   Theorem I.4.20** (the *finitely-generated-module* generalization of I.4.10, explicitly
   titled "Generalization to finitely generated modules," p.66) for its "seven-term exact
   sequence," not I.4.10. The map never mentions I.4.20. This is a genuine gap: the map's
   "finite modules only, no Iwasawa PT needed" framing (§2, AGREED) is true for the
   *deliverable* axiom, but the actual literature proof-chain Wiles used passes through the
   finitely-generated case NSW/Milne also cover — worth a footnote if anyone later re-derives
   8.7.9 from scratch rather than taking it as an axiom.

5. **Analogous Odlyzko-style unsourced-constant hunt.** No unsourced numeric constant found
   (formula constants, group orders, product ranges all check out against primary sources).
   The closest analogue to the Odlyzko panel's finding is item 3 above: a formula presented
   as jointly sourced from two primary texts whose literal statements differ in shape, with
   the gap silently bridged by a third (correctly cited but not foregrounded) source.

## Panel questions (this lens)

- Q1 (descope full 8.6.10/Sha): supported — both are independently stated theorems in NSW,
  confirmed consumer-free claim is a scoping judgment, not a citation error.
- Q3 (axiom shape = order formula, "matching NSW 8.7.9 / Wiles Prop 1.6"): the shape in §5
  item 6 matches NSW 8.7.9 and DDT 2.18 verbatim; matches Wiles 1.6 only after Wiles's own
  h∞-splitting is unwound. Recommend the axiom docstring cite NSW 8.7.9 (or DDT 2.18) as the
  primary source for the *stated form*, with Wiles 1.6 as "the original special case (K=ℚ)."
- Q4 (M* = Hom(M,μ) convention): confirmed consistent across NSW (A₀), Wiles (X*, using μ_p∞),
  and DDT (M*) — safe to freeze as stated.

## Worst finding

The map's ready-to-draft axiom (§5.6) states a formula in exactly NSW-8.7.9/DDT-2.18 shape
while citing "NSW 8.7.9 / Wiles Prop 1.6" as if interchangeable; Wiles's primary-source
statement is narrower (K=ℚ, p-power order X) and structurally different (separate archimedean
term, product only over finite places in Σ). Not a fabrication — DDT bridges it — but the
map should cite DDT 2.18 (or NSW 8.7.9) as the source of the *displayed* formula, demoting
Wiles 1.6 to "originating special case," to avoid a future reader assuming Wiles's paper can
be opened to that exact display.

## Overall verdict

**SOUND, with repairs.** All structural/theorem-number citations (NSW 8.6.7, 8.6.10, 8.7.4,
8.7.8, 8.7.9, 7.1.4, 7.1.8, 7.2.6, 7.3.1; Milne I.4.10) verified against primary-source text,
no errata conflicts. One repair needed: reattribute the exact displayed order-formula shape
to NSW 8.7.9 / DDT 2.18 rather than presenting Wiles Prop 1.6 as a same-shape source, and
optionally add Milne I.4.20 as the generalization Wiles's own proof actually leans on.

File: /Users/kas/FLT/cartography/panel/pt-literature.md
