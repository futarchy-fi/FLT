# CFT + solvable extensions — reconciliation (bead hub-lsb1u.9.4)

Reconciles pass 1 (`cartography/cft:cartography/cft.md`) and pass 2
(`cartography/cft-b:cartography-b/cft.md`). Cross-read against
`cartography/pt-reconciled:cartography/pt-reconciled.md` (PT/CFT boundary) and the
external-repo audit bead hub-lsb1u.9.3 (kbuzzard/ClassFieldTheory,
mariainesdff/LocalClassFieldTheory). Working-tree file only; not committed.
All file:line citations below re-verified directly against the checkout on 2026-08-14.

## 1. Agreement matrix

| Claim | Pass 1 | Pass 2 | Status |
|---|---|---|---|
| All blueprint CFT lives in `chtopbestiary.tex` (local :24-29, global :83-86, SW trick :90-94, PT stub :96) | yes | yes | AGREED |
| **Narrow-seams-first verdict**: state the SW solvable-extension trick as a named assumption (S) instead of building CFT; matches `FLT/Assumptions/README.md:36-37` | yes (slice ordering §, step 2) | yes (§6 verdict, row 2) | AGREED |
| **Full local+global reciprocity is XL and off the critical path** by explicit project design (`knownin1980s`, Assumptions list) | yes ("need not be exposed to every consumer") | yes ("not on FLT's critical path") | AGREED |
| Tame-inertia map (ch04overview.tex:46-47) needs no reciprocity — sub-CFT (unramified + Kummer) | yes (item 2, S–M) | yes (N1, M) | AGREED |
| `cyclic_base_change` takes solvability as an *input* typeclass (`Automorphic.lean:133`), `sorry` at :184; CFT only needed if a caller must *manufacture* E | yes (item 7) | yes (N2) | AGREED |
| SW trick has `\uses{global_class_field_theory}` (chtopbestiary.tex:90) and feeds `modularity_lifting_theorem` (ch04overview.tex:68) | yes | yes | AGREED |
| No local/global Artin map, Lubin–Tate, ray-class existence, Br(K_v) computation, or Poitou–Tate anywhere in pinned Mathlib | yes (missing list 1-6) | yes (§4 absent list) | AGREED |
| Idele/adele substrate exists and is support, not a CFT consumer | yes (item 9) | yes (N9, + Fujisaki done) | AGREED |
| Blueprint staleness: `chtopbestiary.tex:96` "we don't even have Galois cohomology" is outdated (Mathlib `ContCohomology` + FLT cup products exist) | implicit (coverage §) | explicit (risk 4) | AGREED |

## 2. Divergences resolved

### 2.1 Consumer-inventory granularity and the tame-inertia hack
Pass 1 has 9 items sourced mostly from blueprint tex; pass 2 has 9 named consumers (N1–N9)
sourced Lean-first, including the ADMITTED hack pass 1 only brushed against.
**Verified directly**: `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:178`
defines `localTameAbelianInertiaGroup` as the subgroup
`{ σ | ∀ x, x ^ (Nat.card (κ 𝒪ᵥ) - 1) ∈ fixedField (localInertiaGroup v) → σ x = x }`, with
docstring (:172-176) "Note that this definition is somewhat cheating, abusing the fact that the
field corresponding to this subgroup is Kᵘʳ(ᵖ⁻¹√ϖ) ... TODO: show that this is indeed the
right group." The TODO is still open. Downstream uses verified:
`FLT/Deformations/LiftFunctor.lean:132` (deformation condition) and
`FLT/GaloisRepresentation/Automorphic.lean:176` (tame rank-1 quotient hypothesis of
`cyclic_base_change`).

**Soundness grade.** The cheating is **not visible to the kernel and is not an axiom-shaped
hole today**: it is a plain `def` (no `sorry`, no `axiom`), fully elaborated and
kernel-checked. The risk is *specification-level*: the subgroup is defined by a Kummer-theoretic
characterization instead of as the kernel of a constructed map I_v → k(v)^×, and the
equivalence is unproven. Severity is **medium and rising**: today the only things quantifying
over it are a `sorry`'d theorem (`Automorphic.lean:184`) and a functor definition, so nothing
false can be *proved*; but `cyclic_base_change` is destined to become a `knownin1980s`-class
axiom (`FLT/Assumptions/KnownIn1980s.lean:39` names cyclic base change), and the moment it is
axiomatized over the uncertified group, a wrong definition converts into a genuinely false
axiom — an axiom-shaped hole by transmission. **Resolution: adopt pass 2's framing; certifying
the def (M-sized, unramified + Kummer theory only) is promoted to a ready-now item and must
land before the cyclic-base-change axiomatization.**

### 2.2 What does the SW trick's *proof* actually need?
Pass 1: "global reciprocity plus a finite existence/disjointness package"; pass 2: existence
side only — Grunwald–Wang-style cyclic extensions with prescribed local behaviour, "no global
reciprocity map, no Artin map, no cohomological CFT." **Resolution: adopt pass 2 for planning,
flagged (literature-verify)** — the standard existence-theorem route does factor through
ray-class/Grunwald–Wang machinery whose classical proofs use reciprocity, so the *formal*
dependency floor is unresolved; but both passes agree the project-critical slice is the
S-sized *statement* as an assumption, for which the question is moot. All statement vocabulary
exists (`Automorphic.lean:129-136`, `HeightOneSpectrum.preimageComapFinset` at :183).

### 2.3 The modularity-lifting theorem's CFT boundary
Pass 1's item 5 said "from CFT, only item 4's [SW] interface." Pass 2's N4 correctly reads the
full `\uses` list (ch04overview.tex:68-69): SW trick **plus** the local Galois cohomology
quartet (`local_galois_coh_dim_two/top_degree/poincare/euler_poincare`). **Resolution: adopt
pass 2**, and align with the PT reconciliation (§2.1 there), which verified the same list and
ruled the quartet local-only — no global-duality node is cited by MLT.

### 2.4 Boundary with Poitou–Tate (pt-reconciled ruling adopted)
Pass 1 treated PT (its item 8) as a CFT slice; pass 2 kept N4/N5 inside this map. The PT
reconciliation has since fixed the cut and this map defers to it:
**CFT (hub-lsb1u.9) is strictly upstream; its exports to the PT bead are (a) the local
invariant map inv_v: H²(G_{K_v}, μ) ≅ ℚ/ℤ (pt-reconciled node 6, "consumed as black box",
L-sized, upstream) and (b) global reciprocity / sum-of-invariants = 0, i.e. the
class-formation cut "(G_S, C_S) is a class formation" (pt-reconciled node D2, "absorbed into
CFT boundary").** Local Tate duality, local/global Euler characteristics, middle-exactness,
and Greenberg–Wiles are PT-bead work built *on* those exports, not CFT deliverables. Whether
this bead exports raw inv_v + reciprocity or the packaged class formation is pt-reconciled
panel Q2, restated as Q1 below.

### 2.5 Potential modularity's "several nontrivial results in global CFT"
Pass 1 left ch04overview.tex:27-32 as the largest scope uncertainty. Pass 2 concretizes the
likely referent: **N6, GL(1) reciprocity** (Hecke characters ↔ characters of G_K^ab) needed to
even state automorphic induction GL(1)/K → GL(2)/F (chtopbestiary.tex:213-214). **Resolution:
record N6 as the concrete candidate, expected to be absorbed into a `knownin1980s` assumption
with automorphic induction itself; keep pass 1's caveat that the boundary is unfixed until the
proof sketch is expanded (literature-verify).**

### 2.6 Brauer/quaternion seam
Pass 1 classified Brauer hits as non-consumers; pass 2 flags an untracked risk: nothing in
blueprint or Lean states local-global classification of quaternion algebras (Hilbert
reciprocity), yet `Automorphic.lean:100` (`IsQuaternionAlgebra E (E ⊗[F] D) := sorry`) sits on
the N2 path. **Resolution: keep as a watch-item (unbudgeted M–L if it materializes); not a
current consumer.**

### 2.7 External-repo awareness
Pass 1 (repo-only, by rule) reported no ClassFieldTheory package in the lake manifest; pass 2
URL-checked kbuzzard/ClassFieldTheory and mariainesdff/LocalClassFieldTheory. Not
contradictory — different evidence scopes. **Resolution: fold in via the hub-lsb1u.9.3 audit
(§4).**

## 3. Merged consumer-to-slice inventory (with confidence)

Confidence: high = both passes agree and citation re-verified; medium = single-pass or
literature-verify.

| # | Node (consumer → weakest slice) | Refs | Size | Critical path? | Confidence |
|---|---|---|---|---|---|
| 1 | Tame-inertia char: certify `localTameAbelianInertiaGroup` TODO (unramified + Kummer, no CFT) | AbsoluteGaloisGroup.lean:178, :176; consumers LiftFunctor.lean:132, Automorphic.lean:176 | M | yes — blocks sound axiomatization of node 3 | high |
| 2 | Frobenius/unramified bedrock (`adicArithFrob`, `localInertiaGroup`, `IsArithFrobAt`) | AbsoluteGaloisGroup.lean:167,213; Mathlib `RingTheory/Frobenius` | done / S residual | supports 1 | high |
| 3 | `cyclic_base_change`: statement done (`sorry`), solvability an input; destined `knownin1980s` | Automorphic.lean:127-184 | S (stated) | yes | high |
| 4 | SW solvable-extension trick: *state* as named assumption | chtopbestiary.tex:90-94; Assumptions/README.md:36-37 | S | yes — unblocks MLT's CFT edge | high |
| 5 | SW trick *proof*: existence-only route (Grunwald–Wang / ray-class), no reciprocity map claimed | pass 2 N3 | L–XL | no (post-axiom) | medium (literature-verify) |
| 6 | Local Galois cohomology quartet for MLT: statements with explicit maps | chtopbestiary.tex:38-77; ch04overview.tex:68-69 | M–L state / L prove | yes (statement); proof = PT bead | high |
| 7 | **CFT export: local inv_v: H²(G_{K_v}, μ) ≅ ℚ/ℤ** (black box to PT bead) | pt-reconciled node 6; chtopbestiary.tex:52-58 | L | boundary export | high |
| 8 | **CFT export: global reciprocity / Σ inv_v = 0 (class-formation cut)** | pt-reconciled node D2; NSW 8.1 | boundary spec | boundary export | high |
| 9 | Poitou–Tate: descoped to middle-exactness + Greenberg–Wiles, owned by PT bead | pt-reconciled §2.3, nodes 11′/13 | L (there) | cross-bead, not this bead | high |
| 10 | GL(1) reciprocity for automorphic induction (state; likely `knownin1980s` with the induction theorem) | chtopbestiary.tex:213-214; ch04overview.tex:31 | S axiom / XL prove | deferred until potential-modularity expands | medium |
| 11 | Local reciprocity K^× ≅ W_K^ab (Lubin–Tate route) | chtopbestiary.tex:24-29 | XL — outsourced | no | high |
| 12 | Global reciprocity π₀(𝔸_N^×/N^×) ≅ G_N^ab + existence theorem | chtopbestiary.tex:83-86 | XL | no (only 5 and 10 consume it; both axiomatizable) | high |
| 13 | Idele/adele substrate + Fujisaki cocompactness | LocalUnits.lean:75-117; DivisionAlgebra/Finiteness.lean:44-62 | done (M support) | support | high |
| 14 | Brauer/quaternion Hilbert-reciprocity seam (watch-item, currently unstated anywhere) | Automorphic.lean:100; SimpleRing/TensorProduct.lean:23-26 | M–L if it materializes | watch | medium |

**Merged count: 14 nodes** — 5 on the near-term critical path (1, 3, 4, 6, plus export spec
7/8 as interface contracts), 2 done (2, 13), 2 outsourced XL (11, 12), rest deferred/watch.

## 4. External-repo question (audit bead hub-lsb1u.9.3)

Two in-flight external formalizations exist (audited in bead hub-lsb1u.9.3; pass 2 §4
independently URL-verified 2026-08-14):

- **kbuzzard/ClassFieldTheory** — active project to formalize local + global CFT (Clay/Oxford
  2025 school hub); shares the Mathlib `ContCohomology`/`GroupCohomology`/`TateCohomology`
  base that FLT is extending.
- **mariainesdff/LocalClassFieldTheory** (de Frutos-Fernández–Nuccio) — local fields +
  Lubin–Tate; steady Mathlib upstreaming ("PR'ed files" dir; CPP 2024 DVR/local-fields
  foundation already landed). Referenced by the blueprint itself at chtopbestiary.tex:29.

**Port-candidate marking of merged nodes** (deliverable plausibly arrives from the external
pipeline rather than being built in FLT):

| Node | Port candidate? | Source |
|---|---|---|
| 7 (local inv_v) | **yes** | ClassFieldTheory (cohomological local CFT) |
| 8 (reciprocity / class formation) | **yes** | ClassFieldTheory (global track) |
| 11 (local reciprocity, Lubin–Tate) | **yes** | LocalClassFieldTheory + ClassFieldTheory |
| 12 (global reciprocity + existence) | **yes** | ClassFieldTheory |
| 5 (SW-trick proof, existence route) | **yes (partial)** | ClassFieldTheory ray-class/existence layer, if/when it lands |
| 6 (local Galois coh quartet, *proofs*) | yes — but owned by the PT bead's plan | ClassFieldTheory |
| 1, 3, 4, 10, 13, 14 | no — FLT-local statements/certifications | — |

**Port-candidate count: 5** CFT-bead nodes (7, 8, 11, 12, 5-partial); node 6's proofs are a
sixth but are booked to the PT bead. Main port risk = interface drift (pass 2 risk 3): FLT
axiom statements must be written against conventions the external repos can later discharge
(Frobenius normalization, μ vs ℚ/ℤ coefficients).

## 5. Panel questions

1. **Export contract (aligns pt-reconciled Q2):** does this bead export raw inv_v +
   sum-of-invariants, or the packaged class formation "(G_S, C_S)" (NSW 8.1)? PT's
   Greenberg–Wiles descope consumes only the former; ClassFieldTheory's internal architecture
   may prefer the latter. One-directional timeline coupling to the Lubin–Tate effort.
2. **Tame-inertia certification gate:** ratify that node 1 (certify
   `AbsoluteGaloisGroup.lean:178`) must land *before* `cyclic_base_change` is converted from
   `sorry` to a `knownin1980s` axiom, given the transmission risk graded in §2.2. Who owns it?
3. **SW-trick axiom shape:** field-isomorphism vs local-algebra matching of completions,
   solvable vs successive-cyclic tower, and the linear-disjointness clause — freeze before
   drafting the assumption (pass 1's risk list). Also freeze arithmetic-vs-geometric Frobenius
   for every export (pass 2 risk 1: a wrong sign silently corrupts all consumers).
4. **Port-vs-state policy:** for nodes 7/8, does FLT write its own interface now and let
   ClassFieldTheory discharge it later, or wait for their statements to stabilize? Who is the
   liaison to the two external repos?
5. **Potential-modularity boundary:** commission expansion of ch04overview.tex:27-32 to
   confirm whether "several nontrivial results in global CFT" reduces to nodes 4 + 10 or
   hides more (the one remaining scope uncertainty both passes flag).
6. **Brauer/quaternion watch-item:** does any planned step need Hilbert-reciprocity-style
   classification (node 14)? If yes it is unbudgeted; if no, record the dodge (concrete
   discriminant-1 D) as deliberate.

## 6. Ready-now candidates

1. **State the SW solvable-extension trick as a named assumption** (node 4, S) — vocabulary
   all present; matches Assumptions/README.md:36-37; immediately unblocks MLT's
   `Skinner_Wiles_CFT_trick` edge. Gate on panel Q3 conventions.
2. **Certify the tame-inertia definition** (node 1, M) — discharge the
   AbsoluteGaloisGroup.lean:176 TODO via unramified + Kummer theory
   (Mathlib `KummerExtension` + ramification/inertia files suffice per pass 2 §4). No CFT.
3. **State the local Galois cohomology quartet with explicit maps** (node 6 statement, M–L) —
   gated on FLT's own `ContCohomology` cup-product files; coordinate with the PT bead's
   ready-now list to avoid duplicate drafting.
4. **Write the inv_v/reciprocity export spec** (nodes 7/8, S as interface text) — pending
   panel Q1; unblocks both PT and future ClassFieldTheory porting.
5. **Blueprint hygiene** (S): update chtopbestiary.tex:96 staleness and add the missing
   blueprint node for whichever axiom shape Q3 settles.
