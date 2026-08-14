# Galois representations attached to automorphic forms — reconciliation (hub-lsb1u.10.3)

Sources: `origin/cartography/galois-reps` → `cartography/galois-reps.md` (pass 1, "Carayol/Taylor"
8-node map) and `origin/cartography/galois-reps-b` → `cartography-b/galois-reps.md` (pass 2,
14-node G-schema, URL-verified citations). Ledger context: `cartography/jl-reconciled.md`
(Route A ratified, hub-lsb1u.4.3). All repo line anchors re-verified against the working tree at
`/Users/kas/FLT` (HEAD e99f167) on 2026-08-14.

---

## 1. Agreement matrix

| Topic | Pass 1 | Pass 2 | Verdict |
|---|---|---|---|
| Scope: weight 2 only, totally definite `D/F`, discriminant 1, even-degree totally real `F`, `U₁(S)`, trivial character | yes (`Automorphic.lean:56-64`, `:30-35`) | yes (§2 "Which forms") | **AGREED** — no higher weight, no ramified `D`, no odd-degree `F` |
| Compatibility: good-primes only (`v ∉ S`, `v ∤ p`): unramified + `det = N(v)` + `tr = π(T_v)` | yes (`Automorphic.lean:86-95`) | yes (clause (W), `:87-94`) | **AGREED** — verified: the `Prop` at `Automorphic.lean:80-94` quantifies only over good `v` |
| No full local Langlands / Weil–Deligne matching at bad places required | yes (risk 3) | yes ("Not needed" list) | **AGREED** |
| Flatness at `p`, tame rank-1 quotient at `S`, cyclotomic det are *separate consumer hypotheses*, not attachment compatibility | yes (`:117-122` framing) | yes (clauses (Bℓ)/(Bp) as consumer-forced) | **AGREED** (pass 2 sharpens: see §5 risk 1) |
| Attachment theorem not formalized; assumption "forthcoming" (`Assumptions/README.md`) | yes | yes; adds: Hecke algebras now exist so the axiom is **statable today** | **AGREED**, pass 2's addendum verified (`Concrete.lean` HeckeAlgebra exists) |
| Compatible-family API is "weakest possible", good-prime charpolys only (`GaloisRepFamily.lean`) | yes | yes | **AGREED** |
| Edges: hub-lsb1u.4 (JL), .5 (base change), .11 (R=T); blueprint bestiary node `\notready` | yes | yes | **AGREED** |
| Proof-side is XL / out of phase-1 scope; axiom route | yes ("XL" verdict) | yes ("XL, permanently axiomatised") | **AGREED** |

## 2. Divergences resolved

### 2.1 Carayol-vs-Taylor (the load-bearing citation)

Pass 1 frames the attachment throughout as "the Carayol/Taylor attachment", following the Lean
docstring "construction of Carayol, Taylor et al." (`Automorphic.lean:20-26`). Pass 2 (nodes
G6-G8) claims Carayol **structurally cannot** cover the repo's case and that Taylor 1989 is the
theorem that does.

**Verification of pass 2's reasoning — SOUND.** Carayol 1986 (Ann. Sci. ENS 19, 409-468)
constructs the ℓ-adic representations in the cohomology of Shimura *curves* attached to a
quaternion algebra over `F` that is **split at exactly one infinite place** (ramified at the
rest); the curve exists only because of that one split archimedean place. The repo's `D` is
**totally definite** — ramified at *every* infinite place (`Automorphic.lean` docstring; forced
by discriminant 1 + even degree in the campaign's setting) — so there is no split infinite place,
no Shimura curve, and no cohomological realization for Carayol's method to act on. Carayol's
construction cannot be applied to the repo's `D`, directly or after tweaking; the only bridge is
JL transfer to a `GL₂` Hilbert eigenform and back. Independently, for **even-degree** `F` a
weight-2 Hilbert form need not appear in the cohomology of *any* Shimura curve (the classical
"missing case"); this is precisely the gap Taylor 1989 (Invent. Math. 98, 265-280) closed by
congruences + pseudo-representations, deducing the even-degree case from Carayol's odd-degree /
auxiliary-ramification results.

**Verdict: pass 2 wins.** In the repo's exact setting (even-degree `F`, totally definite `D`),
**Taylor 1989 is the chapter's load-bearing citation**. Carayol 1986 is demoted to *upstream
input* (Taylor's congruence argument consumes Carayol's constructions, and Carayol remains the
ℓ ≠ p local-global reference), not the attachment theorem for this bead. Corrections to pass 1:

- Pass 1 map §1 step 2 "Carayol/Taylor attachment", inventory #2, and risk 2 should read
  "Taylor 1989 attachment (even-degree case; builds on Carayol 1986)".
- The Lean docstring "Carayol, Taylor et al." (`Automorphic.lean:20-26`) is acceptable as prose
  but the axiom file (G3) must cite Taylor 1989 primarily. Both are pre-1990, so the
  `knownin1980s` policy (`KnownIn1980s.lean:37-39` names "Taylor and others on attaching Galois
  representations to Hilbert modular forms") is unaffected by the demotion.
- G14 bib gap stands: `blueprint/src/FLT.bib` has neither Carayol 1986 nor Taylor 1989; **add
  both**, with Taylor 1989 attached to the attachment node.

### 2.2 Node schema: 8 vs 14

Pass 2's G-schema strictly refines pass 1's 8 nodes (it separates statement-work from proof-work
and adds the sorried absorbers as first-class nodes). Adopt the G-schema; pass 1 maps into it as:
P1#1→G1(+Hecke infra), P1#2→G3+G7/G8, P1#3→G3 clause (W), P1#4→G10+G13, P1#5→G3 clause (I),
P1#6→G4+G5, P1#7→G9, P1#8→**G15 (new, from pass 1)**. See §6.

### 2.3 Minor

- Pass 1's "route ambiguity" risk (Shimura-variety alternative) is dissolved by 2.1: the
  cohomological route is not merely un-chosen, it is unavailable for this `D`; the bestiary's
  `\uses{Shimura_varieties}` (G13) reflects the GL₂-facing blueprint node, likely superseded per
  the README rephrasing plan. Keep as panel question Q3, not a risk.
- Pass 2's split of compatibility into (W)/(I)/(Bℓ)/(Bp) is adopted as the canonical statement
  decomposition; pass 1's #3/#5/#6 are its coarse-grained ancestors.

## 3. Ledger reconciliation with JL Route A (hub-lsb1u.4.3)

`cartography/jl-reconciled.md` **ratified Route A (absorption)** with a binding rider: every
absorbing axiom must carry a hidden-content ledger, and absorbed content is deferred, never
deleted. Applied here:

1. **G3 (attachment axiom) absorbs one JL direction.** The literature theorem (Taylor 1989)
   takes a `GL₂` Hilbert eigenform; the repo's input is a quaternionic `HeckeAlgebra`
   eigencharacter (`Automorphic.lean:85`). Stating G3 quaternionically bakes in the transfer
   direction *quaternionic eigensystem → Hilbert eigenform*. This matches the JL adjudication's
   list of absorbers (".5/.9/.10"). G3's ledger comment must enumerate: JL transfer (one
   direction) + Taylor 1989 attachment (+ Carayol 1986 upstream).
2. **Double-count rule.** JL content appears in G3, G9 (`cyclic_base_change` — JL both
   directions + mult-one + image classification, per the JL reconciler's verified finding), and
   G10. Per the rule: **credit the JL transfer once, against hub-lsb1u.4**; mark its occurrences
   in G3/G9/G10 as "shared content with hub-lsb1u.4 — do not re-count". In the merged inventory
   (§6) these carry the tag `[shared:.4]`. Symmetrically, the *attachment* content inside G9/G10
   is credited once to **this** bead at G3 and marked `[shared:.10]` there.
3. **Non-blocking hedge** (JL rider 2) is owned by hub-lsb1u.4, not duplicated here; this
   chapter only keeps the pointer.

## 4. Risk items (dedicated section)

### 4.1 Flatness clause (Bp) vs the `knownin1980s` boundary — grade: MEDIUM-HIGH

The consumers (`hρflat`, `Automorphic.lean:150-163`; `IsHardlyRamified` via
`HardlyRamified/Family.lean`) need the attached `ρ_π` **flat (Barsotti–Tate) at `v | p`** when
the level is prime to `p`. The honest general references are **Saito 2009** (Compositio 145,
local-global at p) and **Breuil 1999** (Bull. SMF 127, weight-2 flatness) — both **post-1990**.
A pre-1990 derivation plausibly exists for exactly the needed case (weight 2, level prime to p,
via Carayol's good-reduction models + Raynaud), but it is folklore-shaped and the
`knownin1980s` policy requires a written justification and KMB sign-off (`KnownIn1980s.lean`).
Consequence if it fails the 1980s test: G5 becomes a **separate post-1990 assumption** — a
ledger *category* change, same class as G10/G11's Khare–Wintenberger/BLGGT content. Both passes
flag the neighborhood; pass 2's sharper version is adopted. → Panel Q1.

### 4.2 The sorried instance at `Automorphic.lean:100` — grade: LOW (statement-correctness), with a hygiene rider

**Line verified** in the working tree:
`instance ... : IsQuaternionAlgebra E (E ⊗[F] D) := sorry -- Ask Edison?` at
`FLT/GaloisRepresentation/Automorphic.lean:100` (the file's only other `sorry` is
`cyclic_base_change`'s proof at `:184`).

Two corrections to the framing, then the grade:

- **It is not literally inside a statement.** It is a standalone top-level instance sitting
  *between* `IsAutomorphicOfLevel` (`:67-94`) and `cyclic_base_change` (`:127-184`). The
  `cyclic_base_change` statement does not elaborate through it: its conclusion
  (`:179-183`) applies `IsAutomorphicOfLevel` over `E`, which existentially quantifies its
  **own** `D` over `E` — no `E ⊗[F] D` term appears in the statement. (Grep confirms `:100` is
  the only occurrence of `E ⊗[F] D` in `FLT/GaloisRepresentation/`.)
- **It cannot corrupt a statement even if instance search picks it up.** `IsQuaternionAlgebra`
  is a `Prop`-valued class (`FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean:54`), so the sorried
  instance is a sorried *proof*, proof-irrelevant: any statement elaborated with it means the
  same thing whether the instance is proved or sorried. This is unlike a sorried *data*-carrying
  instance, which genuinely could change a statement's meaning. (The adjacent
  `WithRigidification` is the data-side structure; it is *not* what is sorried here.)

**Grade: LOW statement-correctness risk.** The underlying claim — base change of a quaternion
algebra along a field extension is a quaternion algebra — is true and standard, so the sorry is
a debt, not a landmine. Residual concern (pass 2's, endorsed): it is a repo-wide `sorry` in a
file that will host pinned axioms, and if a future statement (e.g. a restated G9 or a JL hedge)
*does* route through `E ⊗[F] D`, an unproved instance in the elaboration path is bad axiom
hygiene. **Rider: clear it before G9 is pinned as an axiom** — it is on the ready-now list
(also flagged ready-now by the JL reconciliation).

## 5. Merged inventory (15 nodes)

Sizes: S ≤ 1 wk, M ≈ 1 month, L ≈ 1 quarter, XL = multi-year/axiom. Provenance: P1#n / G-n.

| # | Node | Size | Status / tags |
|---|---|---|---|
| G1 | `IsAutomorphicOfLevel` + weight-2 quaternionic form/Hecke interface (`Automorphic.lean:67`; `Concrete.lean` HeckeAlgebra) [P1#1] | S | **done** (modulo G2) |
| G2 | `IsQuaternionAlgebra E (E ⊗[F] D)` instance, `Automorphic.lean:100` | S | sorried; LOW risk (§4.2); ready-now |
| G3 | Attachment axiom statement, clauses (W)+(I) — Taylor 1989 primary citation [P1#2,#3,#5] | S-M to state | not stated; **absorbs JL one direction [shared:.4]**; ledger comment mandatory |
| G4 | Axiom bad-place clause (Bℓ): tame rank-1 quotient at `v ∈ S` [P1#6a] | S extra | not stated |
| G5 | Axiom p-clause (Bp): `IsFlatAt` for `v \| p` [P1#6b] | M extra | not stated; **1980s-boundary risk (§4.1)** |
| G6 | Eichler–Shimura route | — | ruled out (no modular curves in repo's setting) |
| G7 | Carayol route proof | XL | **structurally inapplicable to totally definite D** (§2.1); axiom forever |
| G8 | Taylor 1989 route proof (via JL bridge) | XL | axiom forever; the load-bearing literature theorem |
| G9 | `cyclic_base_change` (`Automorphic.lean:127-184`, sorry `:184`) [P1#7] | XL absorber | statement done; JL/mult-one/attachment content `[shared:.4][shared:G3]` |
| G10 | `mem_isCompatible` (`HardlyRamified/Family.lean:37-68`, sorry `:68`) — compatible family [P1#4] | XL absorber | statement done; **post-1990 content (KW/BLGGT)** — separate ledger class; `[shared:.4][shared:G3]` |
| G11 | `IsHardlyRamified.lifts` (`Lift.lean:37-48`, sorry `:48`) | XL absorber | statement done; post-1990 class |
| G12 | Modularity lifting theorem, Lean statement (blueprint ch04overview.tex) | M | not in Lean; unblocked |
| G13 | Blueprint bestiary GL₂ node (`chtopbestiary.tex:228`, `\notready`) [P1#4 blueprint half] | S doc | likely superseded by G3-G5; panel Q3 |
| G14 | Bib hygiene: add Carayol 1986, **Taylor 1989**, Blasius–Rogawski 1989; Saito 2009/Breuil 1999 for G5 discussion | S | missing |
| G15 | Hecke-eigenvalue/pseudorepresentation bridge into `R = T` patching (edge → hub-lsb1u.11) [P1#8] | L-XL | interface exists (`Automorphic.lean:85,93-94`; `Patching/REqualsT.lean`); packaging literature-verify |

JL transfer content: counted once against hub-lsb1u.4 per §3; G3/G9/G10 marked shared.
Attachment content: counted once here (G3/G8); its echoes in G9/G10 marked shared.

## 6. Panel questions

1. **(Q1, from §4.1)** Does weight-2, level-prime-to-p flatness (G5/Bp) pass the `knownin1980s`
   test via Carayol+Raynaud folklore, or is it a separate post-1990 assumption (Saito/Breuil)?
   Requires written justification + KMB sign-off either way.
2. **(Q2)** G3 statement format: state for `A = ℚ_pᵃˡᵍ` + integrality (I) and derive the general
   `A`-valued form, or state `A`-valued directly (risk: over-asserting beyond the literature)?
3. **(Q3)** Formally supersede the blueprint's GL₂/Shimura-varieties bestiary node (G13) with the
   quaternionic axiom family G3-G5, per the README rephrasing plan?
4. **(Q4)** Do clauses (Bℓ)/(Bp) (G4/G5) go *into* the attachment axiom now, or remain consumer
   hypotheses until the ⇐ directions of G9 are actually needed?
5. **(Q5)** Discriminant-1/even-degree rigidity: accept, or pre-provision the definition for an
   auxiliary ramified `D` (level-raising style arguments)?
6. **(Q6)** Ratify the shared-content ledger of §3/§5 (JL credited to .4; attachment credited to
   .10) as the chapter's double-count rule of record?
7. **(Q7)** G10/G11 ledger class: book the KW/BLGGT content as named modern assumptions now, or
   leave inside the sorried absorbers until phase 2?

## 7. Ready-now

1. **State G3** (attachment axiom, (W)+(I), `A = ℚ_pᵃˡᵍ` form) in a new
   `FLT/Assumptions/`-style file with the mandatory absorption-ledger comment — all
   prerequisites (`HeckeAlgebra`, `GaloisRep`) exist today. Highest value.
2. **Clear the `sorry` at `Automorphic.lean:100`** (true, standard; also on the JL
   reconciliation's ready-now list; prerequisite rider for pinning G9).
3. **G14 bib additions** (Taylor 1989, Carayol 1986, Blasius–Rogawski; Saito 2009 + Breuil 1999
   as G5 discussion refs).
4. **G12**: write the modularity-lifting theorem statement in Lean (blueprint calls it "the
   first target"; ingredients all exist).
5. **Correct pass 1's Carayol framing** (§2.1) in any chapter prose derived from it; keep the
   Lean docstring's "Carayol, Taylor et al." but make Taylor 1989 the primary citation in the
   axiom file.
6. **Draft the G5 1980s-justification memo** for panel Q1 (small, unblocks the ledger-category
   decision).
