# Adversarial panel — CFT dependency honesty (bead hub-lsb1u.9.5)

Lens: DEPENDENCY HONESTY. Reviewed `origin/cartography/cft-reconciled:cartography/cft-reconciled.md`
against `origin/cartography/pt-reconciled:cartography/pt-reconciled.md` and the raw pass-2 source
(`origin/cartography/cft-b:cartography-b/cft.md`), plus direct repo/Mathlib greps. 2026-08-14.

## 1. Export pricing — FAIL on node 8/D2, PASS on node 7 with a caveat

The two exports PT consumes are priced inconsistently:

- **Node 7 (local inv_v: H²(G_{K_v},μ)≅ℚ/ℤ)**: priced **L**, "consumed as black box." This
  undersells it. Classically the invariant map is not separable from local reciprocity — both
  are constructed together via the fundamental-class/dévissage machinery (Serre, *Local Fields*
  XI-XIII), and are comparable in size to "Local reciprocity (Lubin-Tate route)," which the
  *same* document (cft-b §6 row 8) prices **XL, outsourced**. Pricing the invariant map at L
  while its sibling theorem, built from the identical cohomological toolkit, is XL is an
  internal inconsistency, not an honest S/M/L/XL — it reads as the smaller price surviving
  reconciliation because it was needed to keep PT's package M-sized (pt-reconciled §2.6: "sizes
  node 13 at only M given its inputs"). Verdict: node 7 should carry an XL flag or an explicit
  "L only if outsourced to ClassFieldTheory / dFF-Nuccio; XL if proved in-FLT" caveat — the
  current single "L" hides that branch.
- **Node 8 (global reciprocity / Σinv_v=0, class-formation cut) and its PT-side mirror D2**:
  **neither is priced with S/M/L/XL at all.** cft-reconciled node 8's Size column reads
  "boundary spec"; pt-reconciled D2's Size column reads "absorbed into CFT boundary + 10/11′."
  Each document points at the other to avoid grading the actual cost. Σinv_v=0 (the second
  inequality / fundamental exact sequence 0→Br(K)→⊕Br(K_v)→ℚ/ℤ→0) is essentially equivalent in
  difficulty to global CFT itself — cft-b's own table prices "Global reciprocity + existence
  theorem" at **XL, multi-year** (§6 row 9). There is no textbook route to Σinv_v=0 that is
  materially cheaper than proving reciprocity outright. This is exactly "hidden behind narrow
  seams": a genuinely XL-costed theorem is exported as an ungraded "boundary spec" that both
  reconciliations mark **high confidence** — high confidence in the *claim's existence*, not in
  any cost estimate, because no cost estimate was made.

## 2. Seam hidden edges — largely disclosed, one genuine gap confirmed

- **N1 (Kummer-only tame character)**: clean, no hidden edge. Grepped Mathlib —
  `KummerExtension.lean` exists and is genuinely CFT-free (unramified+Kummer). No objection.
- **N3 (existence-only SW producer, Grunwald–Wang/ray-class route)**: cft-reconciled §2.2
  already flags this as unresolved ("literature-verify") rather than hiding it — credit given.
  But the underlying gap is worse than "unresolved": grepped Mathlib and FLT/blueprint for
  `chebotarev`, `dirichlet.*density`, `grunwald` — **zero hits, anywhere.** Classical
  Grunwald–Wang and ray-class existence theorems route through Chebotarev density (or an
  equivalent global-CFT existence argument), none of which is even stubbed. So the "cheap seam"
  claim is correct only for the *statement* (item S in cft-reconciled §6/node 4); the *proof*
  entry (node 5, "L–XL, literature-verify") is optimistic — if the existence route is the one
  eventually chosen, XL undersells it because the prerequisite density theorem doesn't exist in
  Mathlib at all, not even as a stub. Recommend flagging node 5 as XL-plus-missing-prerequisite,
  not just XL.
- **N4 (duality-without-reciprocity)**: this framing is honest, not illusory. Both documents
  correctly isolate that local Tate duality's cup-product pairing needs the invariant map
  (H²≅ℚ/ℤ) as *data* but not the reciprocity isomorphism K^×≅W_K^ab — that is a real
  mathematical distinction (duality is a statement about the pairing being perfect once you have
  *some* iso to ℚ/ℤ; reciprocity is a separate statement about *which* iso). No hidden edge here
  — but see §1: the "cheap" half of that split (inv_v itself) is where the true cost is buried.

## 3. Consumer completeness — inventory holds

Grepped the full FLT tree for `reciprocity|artinMap|localUnits|idele|classFormation|
invariantMap|inv_v|Br(K|BrauerGroup` and blueprint/ for `class field|reciprocity|Weil group|
Artin map`. No consumer outside the N1–N9 (cft-b) / 14-node (reconciled) inventory turned up.
`LocalUnits.lean` hits are idele-substrate support (already node 9/13, correctly non-consumer).
`ch07exampleGLn.tex` "reciprocity" hits are Langlands reciprocity conjectures (unrelated sense),
correctly excluded. Inventory is complete as far as static grep can verify.

## 4. Ready-now audit vs actual state

Node 2 (state SW trick, S) checks out: `FLT/Assumptions/README.md:36-37` lists it under
"Formalizable assumptions... nobody did them yet" — genuinely not started, genuinely ready.
One doc-consistency flag (not a grading issue): the same README lists "Cyclic base change for
GL_2" under "Forthcoming assumptions" ("cannot yet be stated because of missing definitions"),
but `FLT/GaloisRepresentation/Automorphic.lean:127-184` already states `cyclic_base_change` with
a `sorry` — the README is stale relative to Lean. Neither cartography doc flags this
README/Lean drift; worth a one-line correction alongside the already-noted `chtopbestiary.tex:96`
staleness.

## 5. Grade consistency

Internally inconsistent as detailed in §1 (node 7 L vs sibling XL; node 8/D2 ungraded).
Elsewhere sizes track pass-1/pass-2 agreement reasonably (N1 M, N2/N3-state S, N4-state M–L,
N4-prove L, N5-state L, N5-prove XL, Lubin-Tate/global-reciprocity XL) and match the cft-b raw
table without unexplained drift.

File: /Users/kas/FLT/cartography/panel/cft-dependency.md (working tree only, not committed).
