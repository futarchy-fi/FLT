# R = T Modularity-Lifting Core — Reconciled Map

Bead: hub-lsb1u.11.3 · Date: 2026-08-14 · Inputs: pass 1 (`cartography/r-eq-t`,
`8ffb462`, repo-only, no network) and pass 2 (`cartography/r-eq-t-b`, `6746528`,
repo + GitHub API). Working-tree document only; not committed. Gap-fill claims in §4
were re-verified against the live open-PR list on ImperialCollegeLondon/FLT on
2026-08-14 (`gh pr list`/`gh pr view --json files` + `gh pr diff 761`), so §4 is
fresher than either input pass.

---

## 1. Agreement matrix

| Question | Pass 1 | Pass 2 | Agreed |
|---|---|---|---|
| Strategic verdict | Monitoring + gap-filling, not greenfield (§5) | Monitoring + targeted gap-filling; do NOT open an independent front (§6) | **Yes — monitoring + gap-filling** |
| Upstream actively building this chapter | Yes: 2025 Patching/Hecke code, blueprint calls lifting "first target" (ch04overview.tex:112) | Yes: consolidation phase; #1042/#1089/#1071 are the PI's declared next targets | **Yes — upstream is actively building; the empty middle is their declared territory** |
| Generic TW–Kisin patching engine | Done, no sorry in core files | Real-Lean, 14 files ~4,115 lines, exactly 1 peripheral sorry | **Yes — done** (sole sorry: `Patching/Utils/CompactHausdorffRings.lean:42`, = A14) |
| Patching contains no arithmetic | "Instantiated patching data … absent" | "No Galois groups, no Hecke algebras, no deformation rings instantiated" | **Yes — abstract engine awaiting inputs** |
| R=T endpoint is nilradical-kernel only | `ker_RtoT_le_nilradical`, no RingEquiv (`REqualsT.lean:83-101`) | Same, `REqualsT.lean:86` "R = T after reduced quotients" | **Yes** |
| Deformation keystones sorried | `Representable.lean:36-38,101-116`, `LiftFunctor.lean:114-118` | Same lines (38, 106, 117), sized S–L, de Smit–Lenstra cited | **Yes** (= A4) |
| Hecke algebra T real; T-valued Galois reps absent | `Concrete.lean:878-912,1062-1077` done; no attachment/localization | Same; A2 "construction direction" absent, XL | **Yes** |
| Lifting theorem not stated in Lean | Blueprint `\notready`, "very far from even stating" | Same, but flags blueprint staleness — prereqs for the *statement* now largely exist | **Yes — unstated; pass 2's staleness caveat adopted** (= A1, size M) |
| Cyclic base change sorried, analytic wall | `Automorphic.lean:184` sorry noted | A9/A10 (base change, JL, mult. one) = concentrated timeline risk | **Yes — largest risk after duplication risk** |
| PT/Selmer is a future edge, not wired in | No Poitou/Selmer import anywhere in Patching/Deformations (negative search) | PT spent at the `depth Λ = Krull-dim R∞` hypothesis (`REqualsT.lean:76`); upstream provisions via #1110/#1105 as KnownIn1980s | **Yes — PT is upstream-of-A5/A7, currently unwired** |
| `knownin1980s` caveat | Recorded separately, "not a proof" | "Coverage must be read modulo this axiom" | **Yes — all coverage claims are modulo the universal axiom** |

No verdict-level disagreement exists between the passes.

## 2. Divergences resolved

### 2.1 Coverage: ~60% (pass 1) vs ~25–30% (pass 2)

The numbers measure different things and both are correct on their own basis:

- Pass 1's **63% row-count / 55–60% weighted** counts capability rows having *any Lean
  declaration* (proved or sorried) out of 16 rows — a **scaffolding-breadth** metric.
  A sorried statement counts; the empty arithmetic middle is under-penalized because
  infrastructure rows (Hecke, patching) dominate the row list.
- Pass 2's **~25–30% by effort** weights by **remaining proof effort to a sorry-free
  R=T theorem**: patching ~95%, deformation framework ~70%, Hecke definitions ~80%,
  but the XL arithmetic middle (A2–A11) near 0% and the lifting theorem 0%-not-even-stated.

**Agreed single picture (adopt effort basis as headline): the R=T core is ~25–30%
complete by remaining-effort weight, with scaffolding breadth of ~60% (a declaration
of some kind exists for 10/16 capability rows).** The gap between the two numbers *is*
the finding: coverage is concentrated at the two ends (abstract patching engine;
consumer-facing statement shells in HardlyRamified/) with the arithmetic middle empty.
Report the effort number to the panel; use the breadth number only to describe how much
interface surface already exists to build against.

### 2.2 Absent nodes: pass 1's 7 vs pass 2's 15 — merged to 16

Pass 2's A1–A15 is strictly finer-grained; pass 1's node 2 (PT/Selmer dimension input)
has no dedicated A-number, so it is promoted to **A16**. Crosswalk:

| Merged ID | Content | Pass 1 node | Size |
|---|---|---|---|
| A1 | Lean *statement* of the modularity lifting theorem | 7 (part) | M |
| A2 | Galois rep attached to Hecke eigensystem, ρ_π into T_𝔪 | 4 (part) | XL |
| A3 | R → T surjection, T_𝔪 complete local, universality | 4 (part), 6 (part) | L |
| A4 | Corepresentability (de Smit–Lenstra) sorries | 1 (part) | M |
| A5 | Structure theory of R^univ (tangent = H¹, presentation bound) | 1 (part) | L |
| A6 | Local deformation-condition theory (flat at ℓ, narrow-trace at S) | 1 (part) | XL |
| A7 | Taylor–Wiles primes + level-Qₙ systems + depth=dim discharge | 3, 5 (part), 6 (part) | XL |
| A8 | Freeness/finiteness of Hecke module, IsPatchingSystem instance | 5 (part) | L |
| A9 | Skinner–Wiles reduction: cyclic base change (`Automorphic.lean:184` sorry), mult. one | — (pass 1 flagged, unnumbered) | XL |
| A10 | Jacquet–Langlands correspondence | — (pass 2 only) | XL |
| A11 | Potential modularity package (Moret–Bailly #1071, KW/BLGGT) → Lift.lean:48, Family.lean:68 | 7 (part) | XL |
| A12 | 3-adic endgame (`Threeadic.lean:39`, `ModThree.lean:34`) | — (pass 2 only) | L |
| A13 | Frey-curve inputs (`Frey.lean:39,41,46`) | — (pass 2 only; consumption edge) | M |
| A14 | Pontryagin/Peter–Weyl fact (`CompactHausdorffRings.lean:42`) | — (pass 1 footnoted, unnumbered) | S–M |
| A15 | B5/B6 as Lean Props, B4 spine (`Proof.lean`) | — (pass 2 only) | M |
| **A16** | PT/Selmer duality + Greenberg–Wiles/Euler-char dimension formula (the hub-lsb1u.7 spend point; upstream provisioning as KnownIn1980s via #1110/#1105) | 2 | XL |

Pass 1's coarser nodes are unions of these; nothing in either list lacks a merged home.
Dependency edges (pass 2 §4, consistent with pass 1 §2): A1 ← {A2..A11}; A7 ← A5, A6,
A16; A8 ← A10; A11 ← A1 + Moret–Bailly; A12/A13 ← A11; A15 ← A12, A13; Patching/ is
consumed only by A7/A8; hub-lsb1u.10 feeds A2/A3/A11/A13/A15; hub-lsb1u.7 feeds A16.

### 2.3 Weakest sufficient lifting statement

**No mathematical divergence.** Both passes transcribe the same theorem,
`blueprint/src/chapter/ch04overview.tex:66-77` (`\label{modularity_lifting_theorem}`,
`\notready`), with "S-good" = the four bullets at `:49-60`: ℓ ≥ 5; F totally real of
even degree, ℓ unramified in F; S finite, coprime to ℓ; det ρ cyclotomic; unramified
outside S ∪ {ℓ}; trace 2 on tame inertia at S; flat at v | ℓ; ρ̄|_{F(ζ_ℓ)} absolutely
irreducible; ρ̄ modular of level Γ₁(S) ⇒ ρ modular of level Γ₁(S). Pass 1's "Γ₁(S)
form" and pass 2's pinned form are the same statement at different annotation depth.

**Adopt pass 2's pinned form as canonical**, because it adds the load-bearing
operational anchors: the deformation-side Lean shadow is `narrowSLiftFunctor`
(`FLT/Deformations/Representable.lean:95-110` — its four conditions are exactly the
four S-good bullets), and the Frey-side shadow is the sorry pair
`HardlyRamified/Lift.lean:48` + `Family.lean:68`. Retain pass 1's two caveats: the
exact-hypothesis literature reference is `(literature-verify)` (blueprint itself is
unsure, `:79-82`), and the Frey chain consumes only this implication — no full
nine-term PT sequence, no weight variation, no strongest-possible R=T.

## 3. Operations (adopted from pass 2)

- **Fork position**: local tip `e99f167` (2026-08-13, PR #1164) = upstream HEAD;
  0 commits behind at pass-2 time. Mathlib-bump cadence is near-daily (#1172 open).
- **Watch PRs**: #1042 (deformation blueprint chapters toward Gee Prop. 3.24 —
  verified blueprint-verso prose only, no Lean code), #1089 (irred + hardly ramified ⇒
  abs irred over ℚ(ζ_p): a TW hypothesis, feeds A7), #1071 (Moret–Bailly statement,
  feeds A11), #1083 (Ribet's lemma in Slop/KnownIn1980s, feeds A12), #761 (HardlyRamified
  work — see §4), #1110/#1105 (local duality + PT nine-term complex as KnownIn1980s,
  feeds A16). Secondary: #1155 (GL₀ sorries), #1080 (flat ⇒ unramified draft).
- **Sync cadence**: weekly fork sync — already tracked as bead **hub-ox9lw.1** —
  with an event trigger (not full sync) on any PR touching `FLT/Patching/`,
  `FLT/Deformations/`, `FLT/GaloisRepresentation/`, or a merge of any watch PR.
- **Reading of upstream phase**: consolidation/infrastructure, not theorem-landing;
  no substantive math in Patching/ or Deformations/ since mid-July 2026; funded to 2029.

## 4. The four candidate gap-fills — claim status re-verified 2026-08-14

Verified against all 31 open upstream PRs (file lists via `gh pr view --json files`;
diff inspection of #761). Result: **only two of the four are genuinely unclaimed.**

| Gap | Verification result | Status |
|---|---|---|
| **A14** Pontryagin fact (`Patching/Utils/CompactHausdorffRings.lean:42`) | No open PR touches this file. Docstring notes external work at `YaelDillies/mean-fourier` (not an upstream PR — coordination note, not a claim). | **READY NOW** |
| **A4** de Smit–Lenstra corepresentability (`Deformations/Representable.lean:38,106`; `LiftFunctor.lean:117`) | No open PR touches these files (#1172 touches only `RepresentationTheory/` files, mathlib bump; #1042 is blueprint prose only). Upstream *intent* signaled by #1042, so announce before starting. | **READY NOW** (announce first) |
| **A13** Frey hardly-ramified (`HardlyRamified/Frey.lean:39,41,46`) | **CLAIMED by open PR #761** (stepan2698-cpu, non-draft, stale since 2026-01-12): discharges `torsion_isHardlyRamified` via `knownin1980s`, adds `EllipticCurve.torsion_has_rank2`, restructures Frey.lean. | **NOT ready-now** — coordinate/rescue #761, do not duplicate |
| **A12** 3-adic endgame (`Threeadic.lean:39`, `ModThree.lean:34`) | **CLAIMED by the same PR #761**: rewrites Threeadic.lean, proves `three_adic'` modulo a `knownin1980s` `ribets_lemma`, restates `three_adic` (still sorry), adds `has_trivial_quotient` API to ModThree (its sorry remains). Also overlaps #1083 (Ribet's lemma). | **NOT ready-now** — coordinate with #761 + #1083 |

Correction to pass 2: its §6 listed A13 "(coordinating with PR #761)" and A12 as
fillable; the diff inspection shows #761's actual scope is larger than "targets
Frey.lean:46" — it substantially rewrites all four A12/A13 files. Since #761 has been
stale for ~7 months, the right move is a rescue offer on that PR (or panel-approved
takeover with attribution), not independent parallel work.

**Ready-now list: A14, A4.** Best-leverage watch item (not a fill): A1 — merely
*stating* the lifting theorem, the blueprint's own "first target" (ch04overview.tex:112);
treat as upstream's to land, ours to watch.

## 5. Merged inventory

Status legend: done = sorry-free Lean; partial = stated with sorry; absent = negative
search recorded. All modulo `axiom knownin1980s {P : Prop} : P` (KnownIn1980s.lean:79)
and axioms `Mazur_statement`, `Odlyzko_statement`.

| Component | Status | Key evidence (both passes concur) |
|---|---|---|
| Continuous GaloisRep / framed-GL₂ API | done | `Deformations/RepresentationTheory/GaloisRep.lean:47-59,161-172` |
| Pro-artinian category + residue algebra | done | `Deformations/Categories.lean`, `IsResidueAlgebra.lean` |
| Lift/deformation functors + condition functors | partial | `LiftFunctor.lean:102-163`; sorry at `:117` (flat `map`) |
| Representability / universal deformation ring | partial | sorries `Representable.lean:38,106`; `narrowSLiftUniversalRing` via `.choose`; zero structure theory (no tangent dim, no presentation) |
| Abstract Hecke operators | done | `HeckeOperators/Abstract.lean:194-218,256-284` |
| Concrete quaternionic HeckeAlgebra (comm, Noetherian) | done | `Concrete.lean:374-385,878-912,1062-1077`; 0 sorries in ~4,464-line AutomorphicForm tree |
| Finite-dimensional automorphic module | done | `FiniteDimensional.lean:49-70` |
| TW level data (Q as *input* finset) | scaffold only | `Concrete.lean:374-385,850-876`; no existence/adequacy theorem (A7) |
| Generic patching algebra/module/system | done | `Patching/Algebra.lean`, `Module.lean:531-645`, `Over.lean:292-376`, `System.lean` — 1 sorry total in Patching/ (= A14) |
| Abstract R=T endpoint | done (abstract) | `REqualsT.lean:86` `ker_RtoT_le_nilradical`; hypotheses include `depth Λ Λ = ringKrullDim R∞` (`:76`) — the A16 spend point |
| Arithmetic instantiation of patching | absent | A7/A8; negative searches in both passes |
| Hecke → Galois attachment; localized/completed T | absent | A2/A3; `IsAutomorphicOfLevel` compares, never constructs (`GaloisRepresentation/Automorphic.lean:~80-95`) |
| Cyclic base change | partial | sorry `Automorphic.lean:184` (A9); plus S-size instance sorry `:100` |
| Jacquet–Langlands | absent | A10; DivisionAlgebra/ has adelic infra only |
| PT/Selmer/Greenberg–Wiles numerical input | absent | A16; `chtopbestiary.tex:38-77,96`; no Poitou/Selmer/cohomology import in Patching or Deformations; upstream #1110/#1105 provision as KnownIn1980s |
| Modularity lifting theorem | absent (unstated) | A1; blueprint `\notready` `ch04overview.tex:66-77`; statement prereqs now largely exist (blueprint prose stale) |
| HardlyRamified consumption layer | partial | 9 sorries across 8 files (~611 lines): `Lift.lean:48`, `Family.lean:68`, `Threeadic.lean:39`, `ModThree.lean:34`, `Frey.lean:39,41,46` (A11–A13); PR #761 in flight |
| FLT spine | partial | `Proof.lean` `B4_proof := sorry`; B5/B6 are comments, not Props (A15) |

## 6. Panel questions

1. **Coverage basis** — confirm the panel-facing headline is the effort metric
   (~25–30%), with scaffolding breadth (~60%) as a secondary descriptor (§2.1).
2. **PR #761 rescue** — it claims A12+A13 but has been stale since 2026-01-12. Do we
   offer a rescue/completion on the contributor's PR, wait one more sync cycle, or seek
   upstream (kbuzzard) guidance on whether it will be merged or superseded?
3. **A1 collision policy** — stating the lifting theorem is the blueprint's declared
   first target and #1042 is its roadmap. Confirm A1 stays watch-only even though it
   is now size-M and the single best-leverage item.
4. **Axiomatization map** — which absences will upstream route through `knownin1980s`
   vs prove (A16 clearly axiomatized via #1110/#1105; A10 JL? parts of A6?)? This
   determines whether our gap map should track "provable" or "stateable" for each node.
5. **hub-lsb1u.7 handoff** — confirm the PT bead's output is spent exactly at A16
   (Greenberg–Wiles bookkeeping discharging `REqualsT.lean:76`'s depth = Krull-dim
   hypothesis), and whether KnownIn1980s-level statements suffice for that discharge.
6. **Scope of the two ready-now fills** — approve A14 and A4 as active work items
   (A4 with a prior announce on upstream Zulip/issue given #1042's signaled intent;
   A14 with a check on `YaelDillies/mean-fourier` progress first)?
