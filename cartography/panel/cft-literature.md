# CFT chapter — adversarial panel note: literature fidelity (bead hub-lsb1u.9.5)

Target: `origin/cartography/cft-reconciled:cartography/cft-reconciled.md`. Cross-read
`origin/cartography/cft:cartography/cft.md` (pass 1) and `pt-reconciled.md`.

## 1. Skinner–Wiles solvable-extension trick
Paper: C. Skinner & A. Wiles, "Base change and a problem of Serre," Duke Math. J. 107(1)
(2001), 15–25, doi:10.1215/S0012-7094-01-10712-6 — https://projecteuclid.org/euclid.dmj/1091736134
(third of the SW trilogy; §90-94 of chtopbestiary.tex cites this). Abstract confirms the
mechanism: level-lowering "easily achieved if one replaces the base field with a suitable
solvable extension." **UNVERIFIED**: full text is paywalled (no institutional/Sci-Hub access
this session), so pass 1's specific characterization ("no global reciprocity map, no Artin
map... Grunwald–Wang-style, existence-only," cft.md:464) could not be checked against the
paper's actual proof section. Abstract is consistent with, but does not confirm, the
claim — cannot distinguish REFUTED from correct without the primary text.

## 2. Tame-inertia via Kummer/unramified theory only
Claim (chtopbestiary.tex:46-47 route, cft.md:445 "Local, no reciprocity") that the tame
quotient I/wild ≅ lim k(v)^× needs only Kummer theory, matching Serre's standard treatment
(*Local Fields*, ramification-groups chapters). Consistent with the standard fact that the
tame quotient of inertia is described via Kummer extensions K(π^{1/m})/K, pure Galois/Kummer
theory, no CFT. **UNVERIFIED-but-plausible**: could not pull exact Serre *Local Fields*
section text this session (no full-text access attempted beyond search); no contradicting
source found. Not refuted.

## 3. Local duality H²(G_K,μ_n)≅ℤ/n "without the reciprocity map"
Source line: cft.md:478-479, "the one genuinely CFT-flavoured local input — but **not** the
reciprocity isomorphism K^×≅W_K^ab (Serre, *Galois Cohomology* II.5)." Web search confirms
Serre's *Galois Cohomology* Ch. II §5 is exactly where the Brauer-group invariant map
inv: H²(K,μ_n)≅(1/n)ℤ/ℤ is treated, and independently confirms this invariant map **is
itself standardly described as "the invariant map of local class field theory."**
**Important: the cft-reconciled.md document under review does NOT repeat pass 1's
"without reciprocity" framing** — it correctly re-labels this node "CFT import" (§3 node 7;
also pt-reconciled.md node 6, "CFT import... NSW 7.1.4"), consumed as a black box from the
upstream CFT bead. So the reconciled doc is more careful than pass 1 here. Pass 1's phrasing
is a defensible but slippery half-truth: inv_v (top-degree cohomology) and the reciprocity
homomorphism K^×→G_K^ab are logically distinct statements inside a class formation, and in
Tate's cohomological approach inv_v is proved *first*, with reciprocity derived from it via
cup product — so "not literally the reciprocity isomorphism" is technically accurate, but
inv_v is still full local CFT content, not CFT-free. **REFUTED (of pass 1's rhetorical
framing only)**: calling it "no CFT" would be false; it correctly is not what pass 1 said —
pass 1 said "not the reciprocity isomorphism," which is narrowly true but misleading if read
as "doesn't need CFT." The reconciled doc under review avoids this trap. No refutation of
cft-reconciled.md itself on this point.

## 4. External-repo status
- kbuzzard/ClassFieldTheory — **VERIFIED**, https://github.com/kbuzzard/ClassFieldTheory:
  live repo, 315 commits, README states it is the repo for the "2025 Clay Maths summer school"
  on formalizing local+global CFT, has a blueprint site, 3 open issues/4 open PRs — matches
  doc's "active project... Clay/Oxford 2025 school hub" claim.
- mariainesdff/LocalClassFieldTheory — **VERIFIED**, https://github.com/mariainesdff/LocalClassFieldTheory:
  472 commits, contains a "PR'ed files" directory (upstreaming evidence) and an "OldFiles"
  dir, matches doc's "steady Mathlib upstreaming" claim. CPP 2024 DVR/local-fields paper
  precedent (`local_fields_journal` repo) also confirmed to exist independently.

## 5. Unsourced-import hunt (Odlyzko-panel precedent)
Odlyzko panel precedent found a flagship numerical claim traceable only to an unverified
secondary citation. Analogous risk here: cft-reconciled.md and pt-reconciled.md cite pinpoint
NSW (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*) section numbers — 7.1.4, 7.1.8,
7.2.6, 7.3.1, 8.1, 8.6.7, 8.6.10, 8.7.4, 8.7.8, 8.7.9 — and Milne ADT/CFT section numbers,
none of which I could check against the actual book this session (no accessible full text
found). **UNVERIFIED, flagged as import risk**: these are precise enough (theorem numbers,
not just chapter names) to be either exactly right (re-verified, per pass 2's methodology
claims) or silently transcribed/misremembered; I could not independently confirm a single
one. Unlike the Odlyzko case, I found no internal inconsistency (no two passes disagreeing on
a specific NSW number) to trigger a REFUTED verdict — but the citation density here is higher
and less independently checked than the SW/external-repo claims above, so this is the
weakest-sourced part of the document.

## 6. Panel questions (this lens)
1. SW-trick proof mechanism (existence-only vs reciprocity-dependent) — **cannot be settled
   without the paywalled Duke paper**; recommend obtaining full text before freezing the
   axiom-shape decision (panel Q3).
2. Tame-inertia Kummer-only claim — no counter-evidence found; treat as sound pending a
   direct Serre *Local Fields* page check.
3. inv_v "CFT import" labeling in the doc under review is more careful than pass 1 and is
   not refuted; recommend the doc explicitly disclaim pass 1's "not CFT-flavoured" framing
   if it resurfaces elsewhere.
4. External-repo claims (§4) fully verified live against GitHub.
5. NSW/Milne pinpoint citations (§5) are the largest unverified-import surface in this
   chapter and should get a dedicated citation-check pass before the export-spec (node 7/8)
   is frozen.
6. No refutation strong enough to overturn any reconciled-map conclusion; verdict is
   UNVERIFIED-heavy, not REFUTED, on this lens.
