# Moret-Bailly — reconciled map (bead hub-lsb1u.8.3)

Reconciliation of pass 1 (`cartography/moret-bailly`, 7-node map) and pass 2
(`cartography/moret-bailly-b`, 11-node map with the MB-D curve-free interface).
Working-tree document only; verification of MB-D statability performed fresh against
`/Users/kas/FLT` (branch `main`) on 2026-08-14.

---

## 1. Agreement matrix

| Question | Pass 1 | Pass 2 | Agreement |
|---|---|---|---|
| Does the route use MB? | Yes — machinery list (ch04overview.tex:27-28), MLT `\uses` (:71), potential-modularity sketch (:93-98) | Same three citations, same lines | **Full** |
| Role | Taylor-style potential modularity: choose `F, p, E/F` | Same, with Snowden Prop. 10 / Thm 14 as modern template | **Full** |
| Lean implementation status | Zero hits for MB in all `.lean`; gap sits under `B4_proof : B4 := sorry` (`FLT/Proof.lean:98`) | `grep -rni moret` zero outside blueprint; same `sorry` | **Full** |
| Bestiary statement status | `\notready`, curve language absent in Lean (chtopbestiary.tex:255-268/271) | Same, plus typo reports | **Full** |
| Overall size to prove | XL (curves, Ω_v engineering, MLT all XL) | XL; MB6 (MB-1989 heart) and MB8 (twisted modular curve) each independently XL | **Full** |
| Opaque-assumption posture | M/S for a labeled opaque assumption; register under `FLT/Assumptions/`; "track as planned dependency, not completed bypass" | Yes to opaque interface, at MB-D altitude; `knownin1980s` phase-1/phase-2 doctrine cited | **Full on posture; divergence on altitude (§2)** |
| ch02reductions.tex:202 edge | Commented out, non-operative | Same | **Full** |
| Bibliography identity | Moret-Bailly 1989, Skolem I/II, ASENS 22 (FLT.bib:64-78) | Same; Numdam URL live-verified | **Full** |

Both passes independently conclude: **route USES MB for potential modularity; XL to
prove; opaque assumption is the correct campaign posture.**

## 2. Divergences resolved

### 2a. 7-node vs 11-node granularity

Pass 1's 7 nodes are a coarsening of pass 2's 11; no contradictions, only refinement.
Correspondence:

| Pass 1 | Pass 2 | Resolution |
|---|---|---|
| 1. MB statement (XL) | MB2 statement (M given infra) + MB3-MB7 proof-side (S/M/L/XL) | Adopt pass 2's split: statement cost and proof cost are different objects. Pass 1's XL = MB2+MB6+MB7 combined. |
| 2. Curves/moduli (XL) | MB0 curve API (L) + MB8 twisted modular curve (XL) | Adopt split — MB0 is general infra, MB8 is the consumer-specific curve. |
| 3. Field engineering (L-XL) | MB1 (v-adic points, M-L) + MB3 weak approx (S, in Mathlib) + MB4 Krasner (M, core in Mathlib) + MB5 disjointness/Chebotarev (L) | Adopt pass 2: Mathlib anchors (`AbsoluteValue.denseRange_algebraMap_pi`, `IsKrasner`, `LinearDisjoint`) shrink pass 1's estimate; Chebotarev absence keeps MB5 at L. |
| 4. Potential-modularity application (XL) | MB9 good-ordinary locus (M) + MB10 assembly | Adopt split. |
| 5. MLT interface (XL) | Adjacent, out of scope except as consumer | Keep as out-of-scope consumer (matches pass 2's MB10 edge). |
| 6. B4 endpoint / Lean spine | Same evidence (`Proof.lean:98-105`) | Identical. |
| 7. Assumption registration (M opaque / XL proof) | Posture recommendation §6 (MB-D at S-M) | Merged in §4 below. |

**Merged inventory: pass 2's MB0-MB10 spine (11 nodes) + pass 1's two spine-tracking
nodes (Lean B4 endpoint; Assumptions registration) = 13 nodes.** Pass 1's exhaustive
search table and hardly-ramified downstream anchors (`HardlyRamified/Lift.lean:34-48`,
`Family.lean:37-68`) are retained as evidence appendix material — pass 2 did not have
them.

### 2b. STATEMENT ALTITUDE adjudication (the substantive divergence)

Pass 1's weakest-sufficient statement is an application corollary but still phrased over
the bestiary theorem's ambient objects; pass 1 prices the opaque assumption at M and node
1's statement as "currently unexpressible with the available curve language." Pass 2
argues for **MB-D**: a curve-free corollary (given hardly-ramified `ρ̄`, avoidance field,
auxiliary `p`: there exist totally real even-degree Galois `F` disjoint from
`K^avoid`, unramified at `ℓ`, and `E/F` with `E[ℓ] ≅ ρ̄|G_F`, `E[p]` induced from a
character, `E` good ordinary above `ℓ, p`) — statable at S-M with existing repo objects,
hiding MB6+MB8+MB9 inside the opaque node, vs MB-B which would cost ~L just to state
(needs the absent curve API, MB0+MB1).

**Fresh verification of "MB-D uses existing repo objects" (this pass):**

| MB-D ingredient | Repo/Mathlib object | Verified |
|---|---|---|
| Hardly-ramified `ρ̄` | `structure IsHardlyRamified` — `FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96` | ✓ present |
| Elliptic curve over a field | Mathlib `WeierstrassCurve` + `[E.IsElliptic]`, used throughout `FLT/EllipticCurve/Torsion.lean` | ✓ present |
| `E[n]` and its Galois rep | `WeierstrassCurve.nTorsion` (`Torsion.lean:33`); `WeierstrassCurve.galoisRep` (`Torsion.lean:122`) — **declaration exists but body is `sorry`** | ✓ statable (construction pending) |
| Good reduction | `E.HasGoodReduction R` — used as a class instance at `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean:40` and `Flat.lean:128` | ✓ present |
| Totally real + even degree | `NumberField.IsTotallyReal` + `Even (Module.finrank ℚ K)` — exact combination already used at `FLT/Deformations/Representable.lean:56` | ✓ present |
| Linear disjointness | Mathlib `LinearDisjoint` (pass 2 doc-verified; mathlib not vendored locally this pass) | ✓ (pass-2 evidence) |
| "`E[p]` induced from a character" | **No repo declaration** — zero hits for induced/dihedral predicates under `FLT/GaloisRepresentation/` | ✗ gap |
| "ordinary" reduction | **No formal predicate** — only prose comments (`Flat.lean:56`, `QuadraticTwists.lean:182`) | ✗ gap |

**Adjudication: MB-D wins, with a caveat.** The curve-free claim is verified — no
curve/scheme/moduli object is needed, and the heavy ambient objects (hardly-ramified
reps, elliptic curves, torsion Galois reps, good reduction, totally real fields) all
exist under their pass-2 names. But "uses existing repo objects" is ~90% true: two small
vocabulary pieces must be minted first — an "induced from a character" predicate on
`GaloisRep` and an "ordinary (good) reduction" predicate. Both are S-sized definitions
over existing types, so pass 2's **S-M statement cost stands** (at the M end if
`galoisRep`'s `sorry` body must be discharged for the statement to be meaningful; as a
pure statement it need not be). MB-B's ~L statement cost (MB0+MB1 prerequisite) is
confirmed by chtopbestiary.tex:271 and the absence of any curve API. **Resolution: state
MB-D in Lean; keep MB-B (bestiary `moret-bailly`) as a blueprint-only LaTeX node until a
curve API lands (tracked by MB0).**

## 3. Blueprint hygiene (pass 2's bug reports, verified this pass)

All confirmed against the working tree on `main`:

1. **`blueprint/src/chapter/chtopbestiary.tex:258`** — `$\Omega_v\subseteq (L_v)$`
   missing `T`. Fix: `$\Omega_v\subseteq T(L_v)$`.
2. **`chtopbestiary.tex:259`** — literal Unicode `∈` in math mode: `$P ∈ T (L)$`.
   Fix: `a point $P \in T(L)$`.
3. **`chtopbestiary.tex:263`** — `$\Omega_v\subseteq T (L_v) \cong (L_w)$` missing `T`
   before `(L_w)`. Fix: `$\Omega_v\subseteq T(L_v) \cong T(L_w)$`.
4. **`chtopbestiary.tex:264`** (found this pass, same family) — `$\Gal(L_v/K v)$`
   missing subscript. Fix: `$\Gal(L_v/K_v)$`.
5. **`ch04overview.tex:71`** — `moret-bailly` sits in the `\uses{...}` of
   `modularity_lifting_theorem` (env at :66-77), but MB is consumed by the
   potential-modularity step (:93-98), not by the lifting theorem's proof. Fix: when a
   `potential_modularity` node is added to the blueprint, move `moret-bailly` from the
   MLT's `\uses` into that node's `\uses`; until then, add a `%`-comment at :71 noting
   the edge is provisional. (Pass 1 read this edge at face value; pass 2's reading is
   correct — the MLT statement at :74-77 makes no reference to MB.)
6. **Statement-precision items** (pass 2, endorsed): the bestiary statement is silent on
   `S` containing archimedean places (it must — totally-realness is imposed via real
   places) and on quasi-projectivity/properness of `T`. Resolve in any Lean statement;
   Snowden Thm 9 is the template.

These are upstream-report candidates (kevinbuzzard/FLT), not campaign-tree edits.

## 4. Merged inventory + deferred-obligations ledger

**Merged node inventory (13):** MB0 curve API (L) · MB1 v-adic points (M-L) · MB2
bestiary statement (M given MB0-1) · MB3 weak approximation (S, Mathlib) · MB4 Krasner
transfer (M, core in Mathlib) · MB5 linear disjointness + Chebotarev (L; Chebotarev
absent from Mathlib) · MB6 MB-1989 heart: arithmetic surfaces / Picard-Skolem or GPR
large fields (XL) · MB7 assembly (M) · MB8 twisted modular curve `Y(ρ̄_ℓ, ρ̄_p)` (XL;
overlaps Shimura debt, chtopbestiary.tex:246-251) · MB9 good-ordinary locus open+nonempty
(M given MB8) · MB10 potential-modularity assembly (consumer, out of scope) · N12 Lean B4
endpoint tracking (`FLT/Proof.lean:98-105`) · N13 Assumptions registration (S-M for
MB-D; see §2b).

**Deferred-obligations ledger** (charter rule: **deferral is never deletion** — every
obligation swallowed by an opaque node is listed here and survives until proved or
formally retired by panel decision):

| # | Obligation | Size | Hidden inside | Status |
|---|---|---|---|---|
| D1 | MB6 — Moret-Bailly 1989 proof heart (arithmetic models, Picard groups, Skolem machinery; or GPR large-fields route) | XL | MB-D opaque node | **Deferred, XL proof debt** |
| D2 | MB8 — twisted modular curve: representability, smoothness, geometric connectedness | XL | MB-D opaque node | **Deferred, XL proof debt** |
| D3 | MB9 — good-ordinary locus openness/nonemptiness | M | MB-D opaque node | Deferred (revisit with D2) |
| D4 | MB2 — honest bestiary statement in Lean (needs MB0+MB1) | M after L infra | blueprint-only for now | Deferred |
| D5 | `WeierstrassCurve.galoisRep` construction (`Torsion.lean:122` body is `sorry`) | M (Angdinata's division-polynomial work adjacent) | MB-D statement's ambient objects | Deferred, tracked |
| D6 | Induced-from-character predicate + ordinary-reduction predicate | S | must land **before** MB-D is statable | **Not deferrable — prerequisite** |
| D7 | Chebotarev density (MB5 half) | L | MB-D opaque node (disjointness clause) | Deferred |
| D8 | Phase-2 attribution: final assumptions list must cite MB 1989 Thm 1.3 (Skolem II) + Taylor 2002 Prop. 2.1 | S | documentation | Deferred to phase 2 |

## 5. Panel questions

1. **Altitude sign-off**: accept MB-D (curve-free, application-shaped) as the campaign's
   opaque MB interface, with MB-B kept LaTeX-only? (Adjudicated yes here; needs panel
   ratification since it swallows two XL debts, D1+D2, in one node.)
2. **D6 minting**: who defines the induced-from-a-character predicate on `GaloisRep` and
   the ordinary-reduction predicate — this campaign, or upstream FLT? Both are S but
   shape-sensitive (they become part of the phase-2 assumption's trusted surface).
3. **`knownin1980s` vs named assumption**: register MB-D as a fourth module under
   `FLT/Assumptions/` (like Mazur/Odlyzko), or discharge via the `knownin1980s` tactic?
   Pass 2 allows either; a named module is more visible for the phase-2 "final ten."
4. **Precision of MB-D**: does the panel want the auxiliary prime `p` existentially
   quantified inside the node or supplied as an input (pass 2's phrasing takes it as
   input; Snowden Thm 14 chooses it)? Affects consumer ergonomics at MB10.
5. **Upstream hygiene**: file the five chtopbestiary/ch04overview fixes (§3) as an
   upstream PR/issue to kevinbuzzard/FLT now, or batch with the campaign's first
   blueprint contribution?
6. **Shimura-track coupling**: if the Shimura-variety track builds modular-curve
   geometry anyway, should D2 (MB8) be re-scoped from "permanently out of scope" to
   "contingent on Shimura track," per pass 2 §6.3?

## 6. Ready-now candidates

- **R1 (S)**: mint the two D6 predicates (induced-from-character on `GaloisRep`;
  ordinary good reduction extending `HasGoodReduction`) — pure definitions over existing
  types; unblocks MB-D.
- **R2 (S-M)**: state MB-D in Lean under `FLT/Assumptions/` (or `knownin1980s`-guarded),
  with literature comments citing MB 1989 I/II (Numdam-verified), Taylor 2002, Snowden
  L26, Buzzard arXiv:1101.0097 — after R1.
- **R3 (S)**: upstream typo/edge-hygiene report, §3 items 1-5 (exact fixes drafted).
- **R4 (S)**: MB3 weak-approximation glue — Mathlib anchors exist
  (`AbsoluteValue.denseRange_algebraMap_pi` et al.); a short repo-side lemma in the
  number-field shape used by `FLT/NumberField/Completion/` de-risks the proof-side later.
- **R5 (S)**: add ledger §4 cross-references into campaign tracking so D1/D2 XL debts
  stay visible (charter: deferral never deletion).

Not ready: MB0/MB1 (curve API, v-adic point topology — start only if MB-B-in-Lean is
ever mandated), MB6/MB8 (XL research debts, deferred per ledger).
