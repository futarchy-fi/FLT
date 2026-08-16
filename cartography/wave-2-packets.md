# Wave 2 — packet envelopes for the cattle pool (45 Odlyzko leaves + Flash statement tier)

**Author:** fermat (crew-18), 2026-08-16.
**Base:** FLT `origin/main` = `b0fbbec` (merge of PR #8 / hub-oig35.20,
2026-08-16T11:40:11Z). Every target path and line number below was checked against that
tree on this date.

**Baseline moved this morning — a packet still carrying `71` will false-fail.** Two merges
landed within half an hour: PR #7 (C1) changed only the `FLT/MazurW.lean` witness curve, a
proof-body change with delta `[0,0]`; PR #8 closed the four `galoisRepresentation` holes in
`FLT/EllipticCurve/Torsion.lean` with delta `[-4,-4]`. Re-verified at `b0fbbec`:
**56 live / 11 prose / 67 naive.** Every delta below is relative and therefore unaffected,
but the constant each packet is gated against must be re-recorded. See
`oracle-recount.md` §0 for the revision log.
**Companion documents:** `oracle-recount.md` (acceptance-gate correction — read
first, it changes the baseline constant), `aintlib-substrate.md` (the port that supplies
roughly half of §3 in one move).

> **SUPERSEDED IN PART, 2026-08-16T13:0xZ — read `wave-3-packets.md` before dispatching
> anything from this file.** This document is the *inventory*: 55 sized, dependency-ordered
> units. `wave-3-packets.md` is the *executable* layer for the 16 of them that have no unmet
> dependency, with real target paths, `FLT.lean` wiring, delta budgets and acceptance lines.
> It also supersedes two things here: the ready-set table in §2 (re-verified at `daac1f2`)
> and the packet contract in §1, which gains a build-closure clause — `lake build` does not
> compile every file the oracle counts, see `oracle-recount.md` §8.

## 0. Why this wave exists — the terminal target

`FLT/Assumptions/Odlyzko.lean:57` is an **axiom**:

```lean
axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
  (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K
```

The 45 leaves below are the complete decomposition of what it takes to delete that
`axiom` keyword: 24 core nodes for the Dedekind zeta functional equation
(`zeta-fe-decomposition.md`) and 21 nodes for the zero theory of `Λ_K`
(`odlyzko-m3-decomposition.md`). No node in either tree is L or XL. That is the whole
point of the decomposition mandate: this wave is dispatchable to cattle *today*.

## 1. Packet contract (applies to every envelope in this document)

Inherited from the generalized oracle rule, with one correction and two additions.

**Acceptance gate**
1. `lake build` exits 0.
2. Global `sorry`/`admit` count equals `baseline + declared_delta`, delta inside the
   packet's budget. **Baseline is the live count, 56 at `daac1f2` — not 71, and no longer
   the 60 this line originally said** (PR #8 closed four holes). Read it off
   `oracle-recount.md` §0. The counter must strip `--` line comments and `/- … -/` blocks
   before matching; the naive grep counts 11 prose occurrences and will mis-gate.
   `scripts/sorry_count.py --json` is the reference implementation.
3. `git diff` against the base is confined to the declared `write_paths`.
4. For negative deltas: the target theorem *statement* is byte-identical to base (only
   removed lines may be `sorry` lines). Rejects proving-by-weakening.
5. No new `axiom` keyword anywhere in the diff.
6. **(new)** No modification of any line matching `sorry`/`admit` that is not the declared
   target hole. This closes the §4 hazard in the recount document.
7. **(new)** New files must follow the repo's module idiom: `module`, `public import …`,
   `@[expose] public section`, Apache-2.0 header. Every file in `FLT/` on `8ea4f0a` does.

**Base pin:** `daac1f2` (was `8ea4f0a5` when this file was written; main has advanced
twice since). Packets are authored against a SHA; if main advances, the delta budget is
unchanged — all deltas are relative — but the base must be re-recorded in the merge
receipt, per the post-merge rule.

**Citations:** every statement node inherits the citation anchors fixed in
`citation-recheck-2.md`. Do not let a worker re-derive a reference.

## 2. Revalidation of the standing ready set against `8ea4f0a` (post-C1-merge)

*Superseded by `wave-3-packets.md` §2, which re-runs this table against `daac1f2` and
corrects hub-oig35.3's acceptance constants. Kept here for the audit trail.*

| Packet | Verdict | Evidence |
|---|---|---|
| hub-oig35.3 (A14 Pontryagin) | **READY — dispatch as-is** | Hole live at `FLT/Patching/Utils/CompactHausdorffRings.lean:42`, `Group.subsingleton_of_pow_prime_eq_one`; statement unchanged. Delta `[-1,-1]`. Caution: prose occurrence at line 89 of the same file — gate clause 6 applies. |
| hub-oig35.20 v2 (Torsion `DistribMulAction`) | **READY — dispatch, but re-declare** | Holes live at `FLT/EllipticCurve/Torsion.lean:109–112`. The v2 per-field proof routes in `oig35-20-refinement.md` still typecheck against the current signature. **Must add gate clause 6**: prose at line 114 and a trailing comment on line 109 make a −5/−6 miscount the likely failure mode. |
| hub-oig35.10 (`loc_cst`) | **STALE — do not requeue** | Already proved on main. FLT PR #6 is still open with a green check; close or rebase it, do not merge. |
| hub-oig35.5 / .8 / .9 / .11 / .12 / .16 | **UNVERIFIABLE FROM THIS POD** | Target holes recorded only in beads metadata; beads unreachable from crew-18. The inventory in `oracle-recount.md` §2–3 is the full live-hole list, so each is a one-line check the moment beads returns. |

## 3. Wave 2A — Dedekind zeta functional equation (24 core nodes, 26 dispatchable units)

Source: `zeta-fe-decomposition.md`. Route: Hecke's theta-function proof. Sub-nodes `F2a/F2b`
and `F3a/F3b` dispatch separately, so 24 core nodes yield 26 units.

**Everything in Part A is Mathlib-generic** and belongs in `FLT/Mathlib/…` (the repo already
carries 128 such shim files) with an upstream PR to follow. Parts B–D are
`NumberField`-generic. Only E–G are FE-specific.

| Node | Size | Deps | Tier | Target area |
|---|---|---|---|---|
| A1 Dual lattice | S | — | Pro | `FLT/Mathlib/…/ZLattice` |
| A2 Dual covolume | S | A1 | Pro | `FLT/Mathlib/…/ZLattice` |
| A3 Poisson summation on `ℤ^d` | M | — | Pro | `FLT/Mathlib/…/Fourier` |
| A4 Poisson summation over a lattice | S | A1,A2,A3 | Pro | `FLT/Mathlib/…/Fourier` |
| A5 Anisotropic Gaussian + Fourier transform | S | — | Pro | `FLT/Mathlib/…/Gaussian` |
| B1 Trace pairing vs mixed-space pairing | S | — | Pro | `FLT/NumberField/…` |
| B2 Dual of ideal lattice = codifferent | M | A1,B1 | Pro | `FLT/NumberField/…` |
| B3 Covolume of the ideal lattice | S | — | Pro | `FLT/NumberField/…` |
| C1 Theta series: definition, convergence | S | A5 | Pro | `FLT/NumberField/Zeta/Theta` |
| C2 Theta transformation law | M | A4,A5,B2,B3,C1 | Pro | `FLT/NumberField/Zeta/Theta` |
| C3 Unit rescaling invariance | S | C1 | Pro | `FLT/NumberField/Zeta/Theta` |
| D1 Polar decomposition of parameter space | M | — | Pro | `FLT/NumberField/Zeta/Domain` |
| D2 Fundamental domain on norm-one surface | M | D1 | Pro | `FLT/NumberField/Zeta/Domain` |
| D3 Inversion symmetry | S | D1,D2 | Pro | `FLT/NumberField/Zeta/Domain` |
| E1 Kernel: definition, integrability, decay | M | C1,D1,D2 | Pro | `FLT/NumberField/Zeta/Kernel` |
| E2 Kernel functional equation | M | C2,C3,D1,D3,E1 | Pro | `FLT/NumberField/Zeta/Kernel` |
| F1 Partial zeta functions | S | — | **Flash** | `FLT/NumberField/Zeta/Partial` |
| F2a Archimedean Gamma integrals | S | — | Pro | `FLT/NumberField/Zeta/Mellin` |
| F2b Single-point unfolded integral | M | D1,F2a | Pro | `FLT/NumberField/Zeta/Mellin` |
| F3a Unit-orbit ↔ ideal bijection | S | — | Pro | `FLT/NumberField/Zeta/Mellin` |
| F3b Mellin of kernel = completed partial zeta | M | C1,C3,D1,D2,E1,F1,F2b,F3a | Pro | `FLT/NumberField/Zeta/Mellin` |
| G1 `WeakFEPair` packaging | S | E1,E2 | Pro | `FLT/NumberField/Zeta/FE` |
| G2 Completed partial zeta | S | F3b,G1 | Pro | `FLT/NumberField/Zeta/FE` |
| G3 Completed Dedekind zeta + FE | S | F1,G2 | Pro | `FLT/NumberField/Zeta/FE` |
| G4 Continuation of `dedekindZeta` | S | G3 | Pro | `FLT/NumberField/Zeta/FE` |
| G5 M2 interface freeze | S | G3,G4 | **Flash** | `FLT/NumberField/Zeta/Interface` |
| *H1 Residue identification (optional, off critical path)* | M | D2,F3b,G3 | Pro | `FLT/NumberField/Zeta/Residue` |

**Immediately dispatchable (zero unmet deps): A1, A3, A5, B1, D1, F1, F2a, F3a — eight
units, no ordering constraint among them.** At the charter's 3–6 concurrency this is
between one and three hours of pool time and it is the correct opening move.

Recommended first three, in order: **A3** (most load-bearing, upstreamable to Mathlib
as-is), **A1** (small, unlocks the whole B/C column), **F2a** (pure 1-D Euler-integral
substitution).

**Coordination requirement, not optional:** prior art exists for essentially every node in
Parts A–C. The expected mode there is *port + upstream*, not prove-from-scratch — coordinate
with the Mathlib maintainers named in the decomposition (D. Loeffler, X. Roblot, M. Stoll)
and with C. Birkbeck before starting A3/A4 and B2. If the AINTLIB port
(`aintlib-substrate.md`) lands, it supplies roughly 22 of these 24 nodes at once; run
AINTLIB-0 *before* dispatching more than the first eight units, or the pool will prove by
hand what a port would have given for free.

## 4. Wave 2B — zero theory for `Λ_K` (21 nodes)

Source: `odlyzko-m3-decomposition.md`. 13 S + 8 M. Deepest chain is 8 nodes
(N2 → N3 → N10 → N11 → N13 → N16 → N17 → N21), which sets the critical path.

| Node | Size | Deps | Tier | Content |
|---|---|---|---|---|
| N1 FE-interface import | S | M2-tree G1/G4/G5, M1 | **Flash** | statement curation only |
| N2 Exact Γ modulus identities | S | — | Pro | `‖Γ(1+it)‖²`, `‖Γ(1/2+it)‖²` |
| N3 Two-sided vertical-strip Γ bounds | M | N2 | Pro | **the one delicate node** — crude exponents only |
| N4 Digamma strip bound | M | N3 | Pro | discharges the M6 hidden edge |
| N5 Borel–Carathéodory, off-center | S | — | Pro | API glue over `Complex.borelCaratheodory` |
| N6 Holomorphic logarithm on a disk | S | — | Pro | primitive of `f′/f` |
| N7 Landau log-derivative lemma | M | N5,N6 | Pro | the zero-machinery kernel |
| N8 Right-edge two-sided Euler bounds | S | N1 | Pro | `ζ(2)^{−n} ≤ ‖ζ_K‖ ≤ ζ(2)^n` |
| N9 A-priori strip control of `ξ_K` | S | N1 | Pro | |
| N10 Left-edge polynomial bound | S | N1,N3,N8 | Pro | |
| N11 Convexity bound on the strip | M | N3,N8,N9,N10 | Pro | Phragmén–Lindelöf |
| N12 Strip confinement, symmetries, discreteness | S | N1,N8 | Pro | port the `ZetaZeros.lean` pattern |
| N13 Local zero counting | M | N7,N8,N11,N12 | Pro | `m_K(T) ≪_K log T` |
| N14 Convergence weights | S | N13 | Pro | |
| N15 Zero-spacing / admissible heights | S | N13 | Pro | discharges the M3→M4 hidden edge |
| N16 Partial-fraction expansion of `logDeriv ζ_K` | M | N7,N8,N11,N13 | Pro | |
| N17 Horizontal-segment bounds | M | N4,N15,N16,N18 | Pro | |
| N18 `Λ_K` log-derivative decomposition | S | N1,N4 | Pro | |
| N19 Test-function transform decay | M | — | Pro | freezes the Poitou class `𝓕` |
| N20 Absolute convergence of the zero sum | S | N14,N19 | Pro | |
| N21 M3 interface freeze | S | N12–N20 | **Flash** | restatements, no new mathematics |

**Immediately dispatchable: N2, N5, N6, N19 — four units.** N1 can be drafted in parallel
as `sorry`-parametrised hypotheses (that is what makes it a Flash statement packet).

Recommended first three: **N2**, **N5**, **N19**.

**Two contracts a worker must not silently break:**
- N3 must keep crude polynomial exponents. Nothing downstream needs the sharp
  `|t|^{σ−1/2}`, and chasing it turns an M into an L. State this in the packet.
- N19's class `𝓕` is a contract consumed by M7/M8/M9. If a downstream node ever needs a
  discontinuous `F`, N20 becomes conditionally convergent and must be redone with
  symmetric limits — escalate at M7 assembly rather than quietly widening `𝓕`.

## 5. Wave 2C — Flash statement tier (Mazur / CBC)

These are `sorry`-carrying statement scaffolds: positive delta, no proof obligation, cheap
model, high throughput. They are the right load for the Flash tier because the acceptance
gate for them is purely mechanical (compiles, delta in `[1,10]`, paths confined).

**CBC — from `cbc-reconciled.md` §7 "Ready-now statement candidates", dependency-ordered:**

| Unit | Size | Content | Notes |
|---|---|---|---|
| CBC-S2 | S | Norm on Satake data | pure algebra against a stub `SatakeParam` structure |
| CBC-S5 | S | Gluing skeleton: solvable ⇒ tower with prime-cyclic quotients | Mathlib `IsSolvable`/chief series; cf. `FLT/Mathlib/FieldTheory/Galois/Basic.lean:45-46`; two-sided induction stated against S3/S4 as hypotheses |
| CBC-S3/S4 | S–M each | Assumption statements on quaternionic weight-2 eigensystems | the designated `knownin1980s` successors; blocked only on the Hecke-action part of S1 (`HeckeOperators/Concrete.lean`, partially built) |
| CBC-S6 | M | AI-quad assumption statement | independent of S3/S4 |
| CBC-S8 | M | Chebotarev comparison lemma | `ρ ≅ ρ'` from agreeing Frobenius char polys outside a finite set; **usable by three hubs — dispatch early** |
| CBC-S1′ | S | Sharpen the `cyclic_base_change` docstring/interface | `FLT/GaloisRepresentation/Automorphic.lean:127–184`; record D3's level-bound reading and Q2's ramification side condition as TODO hypotheses, no proof |

Note on CBC-S1′: `Automorphic.lean` carries 2 live sorries (lines 100, 184) and the
`cyclic_base_change` hole is one of them. A docstring-only packet there has **delta
`[0,0]`** and must not touch line 184 — gate clause 6.

**Mazur — from `mazur-reconciled.md` §3, Flash-eligible rows only** (the XL D-core is
explicitly *not* in this wave):

| Unit | Size | Content |
|---|---|---|
| MAZ-A4 | S | The three rational 2-torsion points survive in `E/C` for odd ℓ |
| MAZ-D7a | S/M | Formal-immersion criterion — pure commutative algebra (cotangent surjectivity + Nakayama) |
| MAZ-W | S | Statement of `W` from C1–C4 + D9, as the chapter axiom |
| MAZ-A5 | M | Lean rewiring: prove `FreyPackage.mazur` from `W` via the ch03 chain, replacing `knownin1980s` at `FLT/FreyCurve/Mazur.lean:36`; retire the dead `Mazur_statement` at `FLT/Assumptions/Mazur.lean:105` |

MAZ-A5 is the only one of the four with a merge-coordination cost (it touches an
assumption file and a dead declaration upstream). Dispatch it last of the four, and only
after MAZ-W lands.

`FLT/MazurW.lean` currently carries 2 live sorries (`mazur_W` at line 18, `mazur_W_ge11` at
line 27) — those are the C1/calibration targets, already covered by FLT PR #7. Wave 2C must
not touch them.

## 6. Dispatch plan

**Immediate (no unmet dependencies, 12 units, fills 3–6 concurrency for hours):**

```
Pro:    A1  A3  A5  B1  D1  F2a  F3a   N2  N5  N6  N19
Flash:  F1  N1  G5(after G3/G4)  CBC-S2  CBC-S5  CBC-S8  MAZ-A4  MAZ-W
```

**Ordering constraints that actually bind:**
1. Run **AINTLIB-0** (build gate, `aintlib-substrate.md`) before dispatching Wave 2A beyond
   the first eight units. A green AINTLIB-0 makes ~22 of the 24 zeta-FE nodes a port
   instead of a proof.
2. Wave 2B's critical path is 8 nodes deep. Start **N2** in the first batch or the M3 tree
   becomes the campaign's long pole.
3. **CBC-S8** unlocks three hubs; it is the highest-leverage single Flash unit in the wave.
4. Nothing in this wave touches `FLT/MazurW.lean`, `FLT/EllipticCurve/Torsion.lean:109–112`,
   or `FLT/Patching/Utils/CompactHausdorffRings.lean:42` — those belong to C1, hub-oig35.20
   v2 and hub-oig35.3 respectively. Disjointness is by construction, so the whole wave can
   run concurrently with the calibration packets.

**Packet-ready horizon:** 45 Odlyzko leaves + 10 Flash statement units = 55 dispatchable
packets, of which 20 have no unmet dependency today. At 3–6 concurrency and the observed
per-packet times, that is comfortably beyond the charter's 24-hour packet-ready floor even
if every dependent node stalls.
