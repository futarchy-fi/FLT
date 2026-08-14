# Cyclic base change for GL(2) — reconciled map

Bead: hub-lsb1u.5.3 (FLT-on-Lean campaign). Reconciliation of pass 1
(`cartography/cyclic-base-change` branch, `cartography/cyclic-base-change.md`)
and pass 2 (`cartography/cbc-b` branch, `cartography-b/cbc.md`). Working-tree
deliverable only; repo treated as read-only. Verification of contested claims
was done against the current main working tree (2026-08-14).

Sequencing constraint (orchestrator note, bead hub-lsb1u.5): the campaign
charter **forbids unproved axioms in the final theorem**. Pass 2's "permanent
terminal axiom" framing for the trace-formula core is therefore converted to
*sequencing*: state the theorem now at M cost, and schedule the trace-formula
proof stack **last**, as a shared obligation with the Jacquet–Langlands hub
(hub-lsb1u.4). Section 4 is the explicit deferred-proof-obligations ledger.

## 1. Agreement matrix

Both passes agree, independently, on all of the following.

| Topic | Agreed position | Pass 1 anchor | Pass 2 anchor |
|---|---|---|---|
| Primitive shape | Prime-cyclic (all primes, incl. 2) totally-real base change + descent is the primitive; the finite-solvable version is **derived** by iterating a normal/chief series with prime-cyclic quotients, not assumed. | §1 "Weakest sufficient" item 1; node 12 | CBC-min + N10 |
| Consumers | Exactly two blueprint consumers: Skinner–Wiles minimal-case reduction (`ch04overview.tex:86-88`) and the bestiary interface (`chtopbestiary.tex:212-214`); AI-quad feeds the potential-modularity leg (`ch04overview.tex:93-98`). | §1 evidence list | §1 grep evidence |
| Fields | Totally real only; no CM/imaginary base change is ever needed. Quadratic totally imaginary appears **only** in automorphic induction. | item 3 | "Totally real fields only" |
| Descent + image | Existence of BC alone is useless; the route needs Galois-invariance image characterisation, fibers a torsor under characters of `Gal(E/F)` (via CFT), and (strong) multiplicity one to make descent well-posed on eigensystems. | nodes 10, 11 | N4, N7, risk 3 |
| Mult one / JL | Multiplicity one and Jacquet–Langlands transfer are **shared external nodes owned by hub-lsb1u.4**; CBC consumes, never re-proves. FLT's "modular" is quaternionic, so JL conjugation of the statement is unavoidable. | nodes 10, 15; §3 | N7, N8; §4 |
| Trace-formula infra shared with JL | The twisted trace formula, orbital-integral/matching theory, measures, and local harmonic analysis are common XL subnodes with JL's own proof; own once (JL-side), record to avoid double-counting. | nodes 2, 5, 6, 7; §3 | N6 note; §4 |
| AI reduced scope | Automorphic induction only in the degree-2 totally-imaginary (CM) case, weight 2, expected Satake parameters; a general solvable-induction theorem is overreach. Costed independently of CBC. | item 3; node 13 | AI-quad, N9 |
| No Langlands–Tunnell | The route avoids non-Galois cubic base change by design (`FLT/Assumptions/Odlyzko.lean:30-41`); do not add such a node. | item 4 | (implicit: no cubic node) |
| Definition debt | The blocking risk is the missing automorphic-representation / Hecke-eigensystem substrate (`chtopbestiary.tex:214`); slippage hits CBC, JL, and Galois-attachment simultaneously. | risk 1 | risk 1 (N1) |
| Cuspidal/Eisenstein edge | `BC(π)` is cuspidal unless `π` is induced from a character of `E`; the descent direction must handle σ-invariant non-cuspidal data. Easy to state wrongly. | node 9 | N3 caveat, risk 4 |
| Size | Statement layer M (dominated by shared substrate); full proof XL, dominated by the twisted trace formula, cost shared with JL. | §5 verdict | §7 verdict |

## 2. Divergences and their resolutions

**D1. Node count: pass 1's 17 nodes vs pass 2's 12.**
Not a substantive disagreement: pass 1 inventories the full Langlands-1980
proof architecture flat; pass 2 splits statement layer from proof layer and
compresses the proof stack into two nodes (N5, N6). *Resolution:* adopt pass
2's statement/proof split as the organising principle (it matches the
campaign's sequencing needs), but retain pass 1's finer decomposition of the
proof stack **inside the deferred ledger** (§4), where it is needed for honest
XL costing and JL-sharing bookkeeping. Merged inventory: 8 statement-layer
nodes + 6 deferred-proof ledger entries = **14 nodes** (§5).

**D2. Existence of a formal Lean anchor.**
Pass 2 claims "No Lean statement of automorphic base change exists anywhere."
This is **wrong on main**: `FLT/GaloisRepresentation/Automorphic.lean:127-184`
states `theorem cyclic_base_change` (finite solvable totally-real `E/F`,
`Even (finrank ℚ F)`, rank-2 continuous `ρ` over `ℚ_p-alg`, irreducible after
restriction to `G_E`, cyclotomic determinant, integral model flat at `v ∣ p`,
unramified outside `S ∪ {v∣p}`, tame rank-one quotient at each `w ∈ S`;
conclusion `IsAutomorphicOfLevel … S ↔` restricted automorphy at the pulled-back
level `S_E`), ending in `sorry` at `:184`. Pass 1's line-by-line hypothesis
table is accurate (re-verified). Pass 2 is right in a narrower sense: this is a
**Galois-representation-side** formulation using the quaternionic automorphy
predicate (`Automorphic.lean:56-95`); no automorphic-representation-side BC
statement exists, and `GaloisRep.baseChange` (`GaloisRep.lean:213`) is
coefficient base change, a different notion. *Resolution:* keep pass 1's anchor
as the primary formal interface; note that it is stated for **finite solvable**
`E/F` directly, so the prime-cyclic primitive + tower gluing must *derive* it.

**D3. Ramified Shintani local base change: in or out of the statement?**
Pass 1 keeps a local-BC node (its node 4, size L) in the main chain; pass 2
cuts it (N5, "recommend: exclude"), keeping only Satake compatibility at
unramified places. **Verified against the invocation sites, the cut is
correct.** Evidence: (i) the only consumers are `ch04overview.tex:86-88`
(Skinner–Wiles level-`Γ₁(S)` bookkeeping) and `chtopbestiary.tex:212-214`;
neither asks for local base change at ramified places. (ii) The formal
statement (`Automorphic.lean:127-184`) handles ramified places entirely through
"unramified outside `S ∪ {v∣p}`", the tame rank-one hypothesis at `S`, and the
pulled-back level `S_E` — no local character identity appears. (iii) The
Galois-side comparison `ρ_{BC(π)} ≅ ρ_π|_{G_E}` needs only Frobenius
characteristic polynomials at unramified places (Chebotarev against
`compatible_family`, `chtopbestiary.tex:222`, whose `S` is exactly the ramified
set). *One caveat, from pass 1's node 9:* the statement **must** still carry a
level/ramification bound at bad places — `BC(π)` unramified wherever `π` and
`E/F` are, and level dividing the pullback `S_E` — otherwise the
level-`Γ₁(S_E)` conclusion is not expressible. That bound is far weaker than
Shintani's character identities. *Resolution:* ramified local BC (Shintani
1979) is **out of the statement**, in the deferred proof ledger (D-2); the slim
level-bound clause is folded into statement node S3.

**D4. Satake-at-unramified-only scope.** Corollary of D3, and both passes'
texts are compatible: pass 1's "weakest local hypotheses" list already contains
nothing at ramified places beyond the tame rank-one quotient. *Resolution:*
adopted. Statement nodes carry Satake/norm-map compatibility
(`α_w = α_v^{f(w/v)}`) at places unramified for both `π` and `E/F`, plus the
D3 level bound; nothing else locally.

**D5. Prime-degree sufficiency.** Pass 1 warns "do not reduce to quadratic
base change alone" and flags the exact Skinner–Wiles tower as
literature-verify; pass 2 asserts prime-cyclic (arbitrary prime) suffices via
the solvable tower. No real conflict: both take *all* prime degrees as the
primitive. The open point is pass 1's: preservation of the local hypotheses
(irreducibility of the restriction, flatness at `p`, tame rank-one at `S`)
at each stage of the tower is unverified. *Resolution:* primitive = all prime
degrees; tower-preservation goes to panel question Q2.

**D6. "Terminal axiom" (pass 2 §6 risk 5, §7) vs the charter.**
Pass 2 recommends "permanent-axiom status" for the trace-formula core. The
orchestrator note overrides this: **no unproved axioms in the final theorem**.
*Resolution:* converted to sequencing. The statement layer (§5) is formalised
now and temporarily rests on `knownin1980s`-style assumptions
(`FLT/Assumptions/KnownIn1980s.lean:80`, CBC named at `:39`/`:69`) exactly as
the repo already plans; the proof obligations are recorded in the ledger (§4)
with owner and ordering, scheduled **after** the modularity-lifting chain is
complete and **jointly with** hub-lsb1u.4, because the dominant cost (twisted
trace formula, orbital integrals, local harmonic analysis) is shared. Nothing
in the ledger may remain an axiom at final-theorem time.

**D7. Substrate for the statement.** Pass 2 argues for phrasing on quaternionic
weight-2 Hecke eigensystems (`WeightTwoAutomorphicForm`, bestiary line 213
literally says "for totally definite quaternion algebras"); pass 1's anchor is
Galois-side. *Resolution:* both, connected: the campaign-facing interface is
the existing Galois-side `cyclic_base_change` (it is what modularity lifting
consumes), and its eventual discharge factors through a quaternionic
eigensystem statement (S1–S5) plus the attachment edge (S8). Not a fork, a
two-layer interface.

## 3. Sequencing (charter-compliant)

1. **Now (statement layer, M):** S1–S8 of §5, phrased per D3/D4/D7, resting on
   the repo's assumption mechanism. Unblocks Skinner–Wiles reduction and the
   potential-modularity leg.
2. **Mid-campaign:** derive the solvable statement from the prime-cyclic
   primitive (S5); discharge S6–S8 as their hubs (CFT hub-lsb1u.10 edge,
   Galois-reps hub-lsb1u.9) mature.
3. **Last (proof layer, XL, shared with JL):** the ledger of §4, executed as a
   joint trace-formula workstream with hub-lsb1u.4. JL owns the shared
   infrastructure (D-3, D-4, D-5-mult-one); CBC owns the twisted/cyclic-specific
   increments (D-1, D-2, D-6).

## 4. Deferred proof obligations ledger

Every entry must eventually be proved; none may survive as an axiom into the
final theorem. "Owner" = hub that proves it; CBC consumes unless marked.

| # | Obligation | Owner | Size | Discharges | Sources (literature-verify where noted) |
|---|---|---|---|---|---|
| D-1 | Local GL₂ representation theory sufficient for parameters/Satake data (principal series, special, supercuspidal). | shared JL/CBC (hub-lsb1u.4 leads) | L | S1, S3 | Bushnell–Henniart; Langlands 1980 local chapters (literature-verify) |
| D-2 | Local cyclic base change / Shintani lifting: norm map on conjugacy classes, character identities, ramified and archimedean places for the weight-2 class. Out of the statement (D3) but required by the proof. | CBC | L | S3, S4 | Shintani 1979; Langlands 1980 (literature-verify) |
| D-3 | Measures, adelic quotients, orbital integrals, and matching of test functions (`GL₂(F_v)` vs `GL₂(E_w)`), incl. fundamental-lemma-type identities for cyclic GL₂. | JL hub-lsb1u.4 (shared) | XL | S3, S4 | Langlands 1980 chs. 2–3; Labesse Ast. 257; Arthur 2005 (literature-verify) |
| D-4 | Twisted trace formula for GL₂ (`Gal(E/F)`-twist): geometric/spectral sides, truncation, convergence; plus the untwisted formula JL already needs. | JL hub-lsb1u.4 (shared) | XL | S3, S4 | Langlands 1980 chs. 6–11; Saito 1975; Arthur–Clozel 1989 ch. 3 |
| D-5 | Spectral comparison ⇒ existence of `BC_{E/F}(π)` with expected Satake data, level bound, cuspidality dichotomy; strong multiplicity one for GL₂ and inner forms (mult-one part owned by JL). | CBC (mult one: JL) | XL (mult one M/L) | S3, S4, level-bound clause | Langlands 1980 main theorem; Jacquet–Shalika (literature-verify) |
| D-6 | Descent/image theorem proof: σ-invariant cuspidal `Π` descends; fiber = `Gal(E/F)`-character torsor; Eisenstein edge case excluded/handled. | CBC | L | S4 | Langlands 1980 descent chapters (literature-verify) |
| D-7 | AI-quad proof: theta-series/Weil-representation or converse-theorem construction of `AI_{K/F}(χ)` with local compatibility. Independent of the trace-formula stack. | CBC (consumed by hub-lsb1u.9) | L–XL | S6 | Hecke 1926; Jacquet–Langlands ch. 12; Arthur–Clozel 1989 |
| D-8 | Tower preservation: irreducibility of restriction, flatness at `v∣p`, tame rank-one at `S`, and linear disjointness survive each prime-cyclic stage of the chosen chief series. | CBC | M | S5 | Skinner–Wiles (exact tower: literature-verify); panel Q2 |

## 5. Merged inventory (with confidence)

Confidence: **high** = both passes agree and repo-verified; **medium** = one
pass, plausible, or literature-verify pending; sizes S/M/L/XL as in both passes.

Statement layer (deliverable now):

| # | Node | Size | Conf. | Provenance |
|---|---|---|---|---|
| S1 | Hecke-eigensystem/Satake substrate on totally definite quaternionic weight-2 forms (`WeightTwoAutomorphicForm`, `LevelStruct`, Hecke action per `HeckeOperators/Concrete.lean`). Shared with JL and Galois-attachment. | M | high | P1-1/2 ∩ P2-N1 |
| S2 | Norm map on unramified Satake parameters, `α_w = α_v^{f(w/v)}`. | S | high | P1-4(slim) ∩ P2-N2 |
| S3 | CBC-existence statement: prime-cyclic totally-real `E/F`, weight-2 trivial-central-character `π`; `BC(π)` exists with norm-Satake compatibility at mutually unramified places, **level dividing the pullback `S_E` / unramified where `π` and `E/F` are** (D3 bound), cuspidal unless `π` induced from a character of `E`. | S–M | high | P1-8/9 ∩ P2-N3 |
| S4 | CBC-descent statement: σ-invariant cuspidal weight-2 `Π` is in the image; fiber a torsor under `Gal(E/F)^` characters; presupposes strong mult one (imported, hub-lsb1u.4). | S–M | high | P1-10/11 ∩ P2-N4/N7 |
| S5 | Solvable-from-prime-cyclic gluing, deriving the formal `cyclic_base_change` interface (`Automorphic.lean:127-184`) from S3+S4; Mathlib has the group theory. Hypothesis-preservation deferred to D-8. | S (+D-8) | high | P1-12 ∩ P2-N10 |
| S6 | AI-quad statement: `GL₁(K) → GL₂(F)`, `K/F` quadratic totally imaginary, algebraic Hecke character ⇒ weight-2 cuspidal `π` with expected Satake parameters and central character. | M | high | P1-13/14 ∩ P2-N9 |
| S7 | Skinner–Wiles CFT trick edge (`Skinner_Wiles_CFT_trick`, `chtopbestiary.tex:91-97`): solvable `L/K` with prescribed local extensions, linearly disjoint from `K^avoid`. Owned by CFT hub-lsb1u.10; CBC consumes. | M (given GCFT) | high | P1-17 ∩ P2-N11 |
| S8 | Galois-compatibility edge: `ρ_{BC(π)} ≅ ρ_π|_{G_E}` via Chebotarev + `compatible_family` uniqueness; JL conjugation of the statement between GL₂ and the quaternion algebra. Owned jointly with hubs lsb1u.9 / lsb1u.4. | M | high | P1-15/16 ∩ P2-N8/N12 |

Proof layer: ledger entries D-1 … D-8 (§4); confidence high on their necessity,
medium on internal sizing (all analytic references literature-verify).

**Merged count: 14 nodes** (8 statement + 6 net new deferred obligations; D-7,
D-8 shadow S6, S5). Reconciles pass 1's 17 (its nodes 2/5/6/7 collapse into
D-3/D-4; 3→D-1; 4→D-2 + S2; 8/9→S3+D-5; 10/11→S4+D-5/6; 12→S5+D-8; 13/14→S6+D-7;
15/16→S8; 17→S7; 1→S1) and pass 2's 12 (N1–N4, N9–N12 → S1–S8; N5→D-2;
N6→D-3/D-4/D-5; N7/N8 → imported into S4/S8 with proofs in D-5/JL).

## 6. Panel questions

1. **Q1 (level bound wording).** Is "level of `BC(π)` divides the pullback
   `S_E`" the right slim clause for `ch04overview.tex:75-77` bookkeeping, or
   does the eventual Lean proof of the lifting theorem need exact conductor
   control at `w ∣ S` (which would drag Shintani/D-2 back into the statement)?
2. **Q2 (tower preservation, from D5/D-8).** In the intended Skinner–Wiles
   tower, do irreducibility-after-restriction, flatness at `v ∣ p`, and the
   tame rank-one condition at `S` demonstrably survive each prime-cyclic stage
   — and does any stage need `E/F` unramified at `p` as an extra hypothesis the
   formal statement currently omits?
3. **Q3 (Eisenstein edge).** Should S4 exclude σ-invariant non-cuspidal `Π` by
   hypothesis (safe, weaker) or classify them (Langlands' full descent)? The
   totally definite substrate sees only "cuspidal" data — is that protection
   airtight on the eigensystem formulation?
4. **Q4 (interface layer).** Confirm the two-layer design of D7: Galois-side
   `cyclic_base_change` as the consumed interface, quaternionic-eigensystem
   statement as the assumption to be discharged. Or should the assumption be
   restated Galois-side only, deleting the automorphic-side statement work?
5. **Q5 (mult-one descoping risk).** If hub-lsb1u.4 descopes strong
   multiplicity one, S4 is ill-posed on eigensystems — who inherits the M/L
   node? (Pass 2 risk 3; needs an owner decision now.)
6. **Q6 (charter sequencing).** Does the panel accept the §3 plan — statement
   axioms now, joint CBC+JL trace-formula workstream last — as
   charter-compliant, given the charter forbids axioms only in the *final*
   theorem?

## 7. Ready-now statement candidates

Formalizable immediately, in dependency order; none blocked on the analytic
ledger.

1. **S2 (norm on Satake data):** pure algebra once a Satake-parameter type
   exists; can be stated today against a stub `SatakeParam` structure. Size S.
2. **S5 gluing skeleton:** "solvable ⇒ tower with prime-cyclic quotients"
   (Mathlib `IsSolvable`/chief series, cf. `FLT/Mathlib/FieldTheory/Galois/Basic.lean:45-46`)
   and the two-sided induction deriving solvable BC from prime-cyclic BC,
   stated against S3/S4 as hypotheses. Size S.
3. **S3/S4 as assumption statements** on quaternionic weight-2 eigensystems
   (per bestiary line 213), prime-cyclic totally-real, trivial central
   character, D3/D4 local scope — the designated `knownin1980s` successors.
   Blocked only by the Hecke-action part of S1, which is shared and already
   partially built (`HeckeOperators/Concrete.lean`). Size S–M each.
4. **S6 (AI-quad) assumption statement:** independent of S3/S4; needs only the
   `GL₂/F`-side substrate plus algebraic-Hecke-character input from CFT. Size M.
5. **S8 Chebotarev comparison lemma:** `ρ ≅ ρ'` from agreeing Frobenius char
   polys outside a finite set, against `compatible_family`
   (`chtopbestiary.tex:222`) — usable by three hubs. Size M.
6. **Sharpening the existing `cyclic_base_change` docstring/interface**
   (`Automorphic.lean:127-184`): record D3's level-bound reading and Q2's
   possible ramification side condition as TODO hypotheses, without proof.
   Size S.
