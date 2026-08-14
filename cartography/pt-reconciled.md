# Poitou–Tate duality — reconciled map (bead hub-lsb1u.7.3)

Inputs: pass 1 = `cartography/poitou-tate` branch (`cartography/poitou-tate.md`);
pass 2 = `cartography/pt-b` branch (`cartography-b/pt.md`). All blueprint citations
below re-verified against the working tree on 2026-08-14.

## 1. Agreement matrix

| Claim | Pass 1 | Pass 2 | Verdict |
|---|---|---|---|
| Scope is **finite discrete modules** over G_{K,S}; no p-adic/Iwasawa PT needed | yes (§2) | yes (§2-3) | AGREED |
| PT has **no blueprint node** — only the deferral sentence at chtopbestiary.tex:96 | yes | yes | AGREED (verified: line 96) |
| `Assumptions/README.md:65-68` plans PT as an axiom, alias "Greenberg-Wiles long exact sequence" | yes | yes | AGREED |
| **ch03/Frey layer consumes only local cohomology**, never global PT (Tate curve, Kummer/Hilbert 90, finite-flat at 2 and ℓ; the character step uses Minkowski) | yes (§1.6-7) | implicit (MLT is "only blueprint consumer" of bestiary) | AGREED |
| **CFT (hub-lsb1u.9) is strictly upstream**: local inv map + global reciprocity are imports; nothing in PT feeds back into CFT | yes (§4) | yes (§4) | AGREED |
| `Selmer` appears nowhere in FLT/ or blueprint/; no Lean PT consumer exists today | yes | yes | AGREED |
| Odlyzko.lean "Poitou" hits are discriminant bounds, not duality | yes | yes | AGREED |
| Mathlib/FLT status: `ContCohomology` + FLT cup products exist; no arithmetic (local/global field) duality, no Brauer inv, no Selmer | yes (§4 anchors) | yes (§5) | AGREED |
| The **Selmer/Greenberg–Wiles corollary, not the full nine-term sequence, is the weakest consumer-facing statement** | yes (§2, closing paragraph) | yes (§2, sharper) | AGREED in substance; pass 2 sharper (see §2.3) |
| Statement-only axiom package is **M**-sized and is the ready-now work | yes (node 1 = S, interface nodes) | yes (§7) | AGREED |

## 2. Divergences resolved

### 2.1 What does `modularity_lifting_theorem` actually need?
Pass 2 claims: only Greenberg–Wiles (NSW 8.7.9 / Wiles Prop 1.6) + local duality +
Euler characteristics; not the topologized nine-term sequence. **Verified against the
blueprint**: ch04overview.tex:66-71 `\uses{Skinner_Wiles_CFT_trick,
local_galois_coh_dim_two, local_galois_coh_top_degree, local_galois_coh_poincare,
local_galois_coh_euler_poincare, ..., local_galois_coh_finite}` — the declared list is
**local-only**; no global-duality node exists to cite. The proof sketch (ch04overview.tex:84-91)
is Skinner–Wiles reduction + Taylor–Wiles/Kisin patching, whose global-duality content is
exactly the Greenberg–Wiles order formula (tangent-space count; auxiliary-prime sets via
dual-Selmer + Chebotarev). Pass 1's broader "expose the Selmer/dual-Selmer dimension
formula" is compatible but under-specified. **Resolution: adopt pass 2's claim.** The MLT
consumer needs nodes 7, 8, 12, 13, 14 plus middle-exactness (see 2.3) — not node 11 in full.

### 2.2 Sha duality (NSW 8.6.7)
Pass 2: unconsumed by anything in the repo. Pass 1 never cites a Sha consumer either (its
D6b Euler-system discussion imports Kolyvagin–Logachev wholesale as an external theorem
interface). **Resolution: agreed — Sha-duality is out of the package.** If Mazur-discharge
work later needs it, that is a new edge for the D6 bead, not this one.

### 2.3 Nine-term sequence scope
Pass 1 kept the full nine-term sequence as the "robust reusable upper bound" (XL); pass 2
recommends explicitly descoping to **middle-exactness only**:
H¹(G_S,M) → ⊕′_v H¹(G_v,M) → H¹(G_S,M*)^∨, which together with the global Euler
characteristic is how NSW derives 8.7.9. Pass 1's own closing paragraph already conceded
the Selmer corollary is the weakest needed statement. **Resolution: descope. The full
topologized NSW 8.6.10 (strict morphisms, restricted-product topology, Pontryagin duals of
non-compact groups) is consumer-free and is the gold-plating risk pass 2 names.** Mathlib
may want it eventually; it is not on this bead.

### 2.4 Skinner–Wiles trick placement
Pass 2 insists SW belongs to CFT, not PT. **Cross-check of pass 1's consumer list:** pass 1
§1 table (chtopbestiary.tex:79-94 row) already marks the SW trick as CFT-upstream and never
lists it among PT consumers §1.1-1.7. Blueprint verified: `Skinner_Wiles_CFT_trick`
`\uses{global_class_field_theory}` (chtopbestiary.tex:90). **Resolution: no real divergence;
both passes place SW in bead hub-lsb1u.9. Recorded to prevent future misfiling since it sits
in the same bestiary section and in the MLT `\uses` list.**

### 2.5 Hidden Mazur/2-descent consumers (pass 1 only)
Pass 1 recovers D6a/D6b and latent B2/C1-C4 2-descent edges from the Mazur panel; pass 2
scoped to the repo and found none. Not contradictory: those consumers are real **only in
the Mazur-discharge phase** (post-axiom; Mazur is currently discharged via
`knownin1980s`, FLT/FreyCurve/Mazur.lean:30-36). **Resolution: keep them as deferred
edges with the fppf/finite-flat bridge (pass 1 node 7) attached to the D6a edge, off this
bead's critical path.** Same treatment for pass 1's hypothetical "CFT replacement of the
Minkowski step" in ch03 — latent, not current.

### 2.6 Granularity and sizing
Pass 2's 14-node inventory is finer and Mathlib-aware (e.g. splits continuous-cohomology
plumbing 1/2/3, archimedean node 9, sizes node 13 at only **M** given its inputs); pass 1's
9 nodes bundle these. **Resolution: adopt pass 2's granularity as the spine, folding in
pass 1's two extra items (fppf bridge; local-global/reciprocity compatibility) as explicit
deferred/absorbed rows.**

## 3. Merged node inventory (with confidence)

Sizes are incremental cost in this repo. Confidence = both passes agree and blueprint/Mathlib
evidence checked (high), single-pass or literature-verify only (medium).

| # | Node | Refs | Size | In descoped package? | Confidence |
|---|---|---|---|---|---|
| 1 | Continuous cohomology of profinite groups; discrete-comparison over finite quotients | NSW 1.2/1.5; Mathlib `ContCohomology` TODO | M | yes (blocks everything) | high |
| 2 | Cup product on continuous cohomology | NSW 1.4; FLT `CupProduct.lean` | S (residual) | yes | high |
| 3 | LES, inflation–restriction, Shapiro (continuous) | NSW 1.3/1.6 | M | yes | high |
| 4 | Local: H¹_nr and finiteness of Hⁱ(G_{K_v},M) | NSW 7.1.8; Serre II.5; = `local_galois_coh_finite` | M | yes | high |
| 5 | Local: cd(G_{K_v}) = 2 | NSW 7.1.8; = `local_galois_coh_dim_two` | S/M | yes | high |
| 6 | Local inv: H²(G_{K_v},μ) ≅ ℚ/ℤ — **CFT import** | NSW 7.1.4; = `local_galois_coh_top_degree` | L (upstream bead) | consumed as black box | high |
| 7 | Local Tate duality (perfect cup pairing) | NSW 7.2.6; Milne I.2.3; = `local_galois_coh_poincare` | L | yes | high |
| 8 | Local Euler characteristic | NSW 7.3.1; Milne I.2.8; = `local_galois_coh_euler_poincare` | L | yes | high |
| 9 | Archimedean/Tate-modified terms | NSW 7.2 rem.; Mathlib `TateCohomology` | S | yes | high |
| 10 | Global G_{K,S}, Hⁱ(G_S,M), restricted product Pⁱ (defs; decomposition groups via chosen embeddings, ch04overview.tex:44) | NSW 8.1/8.6.1 | M/L | defs only | high |
| 11 | Nine-term PT sequence, full topologized (incl. Sha duality NSW 8.6.7) | NSW 8.6.10; Milne I.4.10 | XL | **NO — descoped to 11′** | high |
| 11′ | Middle-exactness: H¹(G_S,M) → ⊕′_v H¹(G_v,M) → H¹(G_S,M*)^∨ | NSW proof of 8.7.9 | L | yes | high |
| 12 | Global Euler characteristic | NSW 8.7.4; Milne I.5.1 | L | yes | high |
| 13 | **Greenberg–Wiles order formula** (Selmer/dual-Selmer) | NSW 8.7.9; Wiles Prop 1.6; DDT §2 | M (given 7,8,11′,12,14) | yes — the workhorse | high |
| 14 | Selmer group of local conditions L; dual conditions L^⊥ | NSW 8.7.8 | S/M | yes (needed even to state 13) | high |
| D1 | fppf/finite-flat local-condition bridge at v∣p (Cartier-dual compatible) | Milne ADT III; pass 1 node 7 | XL | **deferred** → Mazur D6a discharge / ch03 flat conditions | medium |
| D2 | Local-global reciprocity compatibility (sum of invariants; class-formation cut "(G_S,C_S) is a class formation", NSW 8.1) | NSW Ch. 3-6, 8 | absorbed into CFT boundary + 10/11′ | boundary spec | high |

Merged count: **16 nodes** (14 spine incl. 11′ replacing 11, + 2 deferred/boundary), of
which **12 are in the descoped weakest package** (1-5, 7-9, 10-defs, 11′, 12, 13, 14; node 6
imported from CFT).

## 4. Panel questions

1. **Descope ratification:** confirm the bead deliverable excludes full NSW 8.6.10 and Sha
   duality (consumer-free per both passes), targeting middle-exactness + Greenberg–Wiles.
   Does anyone speak for Mathlib wanting the general topologized theorem now?
2. **CFT interface contract:** is the cut "(G_S, C_S) is a class formation" (NSW 8.1) the
   agreed export surface of hub-lsb1u.9, or does that bead export only inv_v + reciprocity,
   leaving class-formation packaging to PT? Timeline coupling to the Lubin–Tate local CFT
   effort is one-directional and tight.
3. **Axiom shape:** should the planned `Assumptions` axiom be the Greenberg–Wiles *order
   formula* (one equation, pass 2's proposal, matching the README alias) rather than any
   exact sequence? Sign-off needed before drafting, since ch04's `\uses` list currently
   undercounts and a blueprint node must be added.
4. **Conventions to freeze before Lean:** M* = Hom(M, μ) vs M∨(1); archimedean (Tate-modified)
   terms; choice of S; decomposition groups via fixed embeddings (ch04overview.tex:44).
   Who owns the convention note?
5. **Deferred-edge bookkeeping:** where do the fppf bridge (D1) and the latent Mazur
   D6a/D6b + 2-descent PT edges live — this bead's backlog or the Mazur-discharge bead?
6. **Coordination:** Livingston–Yang–Hill own the continuous-H¹ critical path
   (README.md:65-66); how does this bead's statement-only work avoid colliding with theirs?

## 5. Ready-now candidates (statement-only axiom package, M — both passes' verdict)

Draftable now against existing `ContCohomology` + `absoluteGaloisGroup`, no proofs:

1. **Def** `H¹_nr`: the unramified subgroup H¹(G_{K_v}/I_v, M^{I_v}) ⊆ H¹(G_{K_v}, M)
   for finite discrete M (node 4, def part).
2. **Def** dual module `M* = Hom(M, μ)` with its G-action (convention frozen per panel Q4).
3. **Given map** (not proved perfect): local pairing
   H¹(G_{K_v}, M) × H¹(G_{K_v}, M*) → ℚ/ℤ, enough to define `L^⊥` (node 7 as interface).
4. **Def** global objects: G_{K,S}, Hⁱ(G_{K,S}, M), localization maps to H¹(G_{K_v}, M)
   via fixed embeddings (node 10, defs).
5. **Def** Selmer group `H¹_L(K,M)` for local conditions L = (L_v), L_v ⊆ H¹(K_v,M) with
   L_v = H¹_nr for almost all v; dual conditions L^⊥ = (L_v^⊥) (node 14).
6. **Axiom (the deliverable)** — Greenberg–Wiles order formula (NSW 8.7.9 / Wiles Prop 1.6):
   for K a number field, M a finite G_{K,S}-module, L local conditions as above, both Selmer
   groups are finite and
   #H¹_L(K,M) / #H¹_{L^⊥}(K,M*) = (#H⁰(K,M)/#H⁰(K,M*)) · Π_v (#L_v / #H⁰(K_v,M)),
   the product over all places (all but finitely many factors 1).
7. **Blueprint node** to accompany it, and the missing `\uses` edge from
   `modularity_lifting_theorem` (ch04overview.tex:66) to the new node — fixing the
   undercount both passes flagged.
