# Poitou–Tate duality — cartography pass B (bead hub-lsb1u.7.2)

Second independent pass. Sources: repo main working tree at `/Users/kas/FLT`, my own
knowledge, web-checked citations. No cartography/ or cartography-b/ material consulted.

## 1. Every mention in the repo (grep evidence)

| Where | What |
|---|---|
| `FLT/Assumptions/README.md:68` | "Poitou-Tate (aka the 'Greenberg-Wiles long exact sequence')" — listed under **Forthcoming assumptions**, "can't be stated yet because we don't have Galois cohomology. This is work in progress by Livingston, Yang and Hill." (`README.md:65-66`) |
| `blueprint/src/chapter/chtopbestiary.tex:96` | "We also need Poitou-Tate duality; I'll refrain from writing it down for now, because we don't even have Galois cohomology in Lean yet (although we are very close to it)." — **PT is not yet a blueprint node.** |
| `blueprint/src/chapter/chtopbestiary.tex:38-77` | The *local* Galois-cohomology bestiary, all `\notready`: `local_galois_coh_finite` (:39), `local_galois_coh_dim_two` (:47), `local_galois_coh_top_degree` (:53), unlabeled `H^2(K,μ_∞)=Q/Z` (:61), `local_galois_coh_poincare` (local Tate duality via cup product, :67), `local_galois_coh_euler_poincare` (:75). Citations all to Serre, *Galois Cohomology* II.5. |
| `blueprint/src/chapter/ch04overview.tex:66-77` | `modularity_lifting_theorem` `\uses{..., local_galois_coh_dim_two, local_galois_coh_top_degree, local_galois_coh_poincare, local_galois_coh_euler_poincare, ..., local_galois_coh_finite}` — the **only blueprint consumer** of the cohomology bestiary. |
| `FLT/GlobalLanglandsConjectures/GLzero.lean:26` | "Wiles' work used class field theory (in the form of global Tate duality) crucially in a central proof that a deformation ring R was isomorphic to a Hecke algebra T." — narrative only, not a dependency. |
| `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/{Basic,CupProduct}.lean` | Live Lean work: coinduced-resolution API and **cup products on continuous group cohomology** (`CupProduct.lean:33`, `ContinuousCohomology.cup`; ~570+ lines), "Material destined for `Mathlib.RepresentationTheory.Homological.ContCohomology`" (`Basic.lean:36`). |
| `FLT/Assumptions/Odlyzko.lean:23,45` | Poitou's *discriminant bounds* — same name, unrelated to duality. Not a consumer. |

`Selmer` appears **nowhere** in `FLT/` or `blueprint/` (grep: zero hits). Neither do
`Poitou-Tate`, `nine-term`, or `Greenberg` outside the two lines above.

## 2. Consumers and what each really needs

1. **`modularity_lifting_theorem`** (ch04overview.tex:66; proof sketch :84-91 = Skinner–Wiles reduction + Taylor–Wiles/Kisin patching in the minimal case).
   - *Declared* needs: only the **local** bestiary (finiteness, cd≤2, inv map, local duality, local Euler characteristic).
   - *Actual* needs (undeclared because PT was never written down, bestiary:96): the
     **Greenberg–Wiles formula** comparing #Selmer / #dual-Selmer (Wiles, *Modular elliptic
     curves and FLT*, Prop. 1.6 = NSW Thm 8.7.9) — used twice: (a) tangent-space dimension
     count for R_∞, (b) existence of Taylor–Wiles auxiliary prime sets via dual-Selmer
     annihilation + Chebotarev. **Weakest sufficient statement: Greenberg–Wiles formula for
     finite modules over G_{K,S} + local Tate duality + both Euler-characteristic formulas.**
     The full topologized nine-term sequence is *not* required by this consumer; only
     "exactness in the middle" (H¹(G_S,M) → ⊕'_v H¹(G_v,M) → H¹(G_S,M*)^∨) plus the global
     Euler characteristic, which is how NSW derives 8.7.9.
2. **`FLT/Assumptions/README.md:68`** (planned axiom file). Near-term need is
   **statement-only**: continuous H¹ of local and global Galois groups, unramified local
   subgroup H¹_nr, dual module M* = Hom(M, μ), local duality pairing to define L^⊥, and the
   Selmer group of a collection of local conditions. Weakest statement: the Greenberg–Wiles
   order formula, stated as one `axiom` (matching the README's "Greenberg-Wiles long exact
   sequence" alias — the axiom can be the formula, not the sequence).
3. **`FLT/Deformations/`** (deformation functors, `Representable.lean` placeholders).
   Future consumer: tangent space = H¹(G,ad ρ̄), Selmer conditions. No cohomology imported
   yet (grep: no H¹/cohomology references). Needs only H¹ + local conditions machinery, no
   duality.
4. **`Skinner_Wiles_CFT_trick`** (chtopbestiary.tex:90) — consumer of *global CFT*
   (bead hub-lsb1u.9), **not** of PT. Listed to fix the boundary (see §4).

No consumer in the repo needs the **full nine-term exact sequence with its topologies**
(strict morphisms, restricted-product topology, Pontryagin duals as topological groups).
The perfect duality of Sha groups (NSW 8.6.7) is likewise unconsumed.

## 3. Node inventory (NSW route, with Milne ADT cross-refs)

Primary reference: Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.
(free electronic edition, Version 2.3, at
https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/ — URL live, checked 2026-08-14).
Cross-ref: Milne, *Arithmetic Duality Theorems*, https://www.jmilne.org/math/Books/ (PDF
`ADTnot.pdf` fetched and confirmed live 2026-08-14; local duality I.2.3, PT sequence
I.4.10, global Euler characteristic I.5.1). Wiles Prop 1.6 alt.: Darmon–Diamond–Taylor
§2.

| # | Node | Ref | Size | Notes |
|---|---|---|---|---|
| 1 | Continuous cohomology of profinite groups; comparison with colimit over finite quotients / discrete `groupCohomology` | NSW 1.2, 1.5 | **M** | Mathlib `ContCohomology` exists; discrete comparison is an explicit TODO in `Mathlib/.../ContCohomology/Basic.lean` |
| 2 | Cup product on continuous cohomology | NSW 1.4 | **S** (residual) | Already ~done in `FLT/Mathlib/.../CupProduct.lean`, upstreaming pending |
| 3 | LES, inflation–restriction, Shapiro for continuous cohomology | NSW 1.3, 1.6 | **M** | Mathlib has these for discrete `groupCohomology` only |
| 4 | Local: unramified classes H¹_nr, finiteness of H^i(G_{K_v},M) | NSW 7.1.8; Serre II.5.2 Prop 14 | **M** | = `local_galois_coh_finite` |
| 5 | Local: cd(G_{K_v}) = 2 | NSW 7.1.8; Serre II.5.3 Prop 15 | **S/M** | = `local_galois_coh_dim_two` |
| 6 | Local: inv: H²(G_{K_v}, μ) ≅ Q/Z | NSW 7.1.4; Serre II.5.2 | **L** | = `local_galois_coh_top_degree`; **this is the CFT import** (Brauer group of local field) |
| 7 | Local Tate duality (perfect cup-product pairing) | NSW 7.2.6; Milne I.2.3 | **L** | = `local_galois_coh_poincare`; needs 2+6 + Pontryagin duality of finite modules |
| 8 | Local Euler characteristic h⁰h²/h¹ = ‖#M‖_v | NSW 7.3.1; Milne I.2.8 | **L** | = `local_galois_coh_euler_poincare` (bestiary states the p∤#M case, "=0") |
| 9 | Archimedean places: Tate cohomology Ĥ^i(Gal(C/R), M), modified terms | NSW 7.2 rem. | **S** | Mathlib has `TateCohomology/Basic` for finite groups |
| 10 | Global: G_{K,S}, H^i(G_S, M), restricted product P^i(K_S, M) with topology | NSW 8.1, 8.6.1 | **M/L** | needs FLT's `absoluteGaloisGroup` + decomposition groups at v (chosen embeddings, `ch04overview.tex:44`) |
| 11 | Nine-term Poitou–Tate exact sequence | **NSW 8.6.10**; Milne I.4.10 | **XL** | topologized, strict morphisms; the duality of Sha's (NSW 8.6.7) is the same package |
| 12 | Global Euler characteristic formula | NSW 8.7.4; Milne I.5.1 | **L** | |
| 13 | Greenberg–Wiles formula for Selmer/dual-Selmer orders | **NSW 8.7.9**; Wiles Prop 1.6 | **M** (given 7, 8, 12, middle-exactness of 11) | the actual FLT workhorse |
| 14 | Selmer group of local conditions L = {L_v}; dual conditions L^⊥ | NSW 8.7.8 | **S/M** | definition layer; needed even for the statement of 13 |

**Statement-only package for the planned `Assumptions` axiom** (README:68): nodes 1, 4
(H¹_nr def only), 7 (pairing as a *given map*, no perfectness proof), 10 (defs), 14 →
**M overall**. Livingston–Yang–Hill's ContCohomology work is exactly this critical path.

## 4. Dependency edges and the CFT boundary (bead hub-lsb1u.9)

```
CFT bead (hub-lsb1u.9)                          PT bead (this one)
────────────────────────                        ─────────────────────────────
local CFT: inv_v : Br(K_v) ≅ Q/Z  ──────────▶  6 ──▶ 7 ──▶ 8
  (fundamental class / Lubin–Tate;                       │      │
   de Frutos-Fernández & Nuccio,                          ▼      ▼
   chtopbestiary.tex:29)                        11 ◀── 10, 9    13 ◀── 12, 14
global CFT: class formation for C_K,   ────────▶ 11, 12
  reciprocity Σ_v inv_v = 0 (ABHN seq)
global_class_field_theory (bestiary:83) ──▶ Skinner_Wiles_CFT_trick (bestiary:90)  [CFT bead, NOT PT]
```

**Boundary, precisely:** everything up to and including the local invariant isomorphism
(node 6) and the global "sum of invariants is zero / Br(K) ↪ ⊕Br(K_v)" exact sequence is
CFT-bead territory; PT consumes them as black boxes. NSW proves Ch. 7–8 from the class-
formation axioms of Ch. 3–6 — the clean formal cut is **"(G_S, C_S) is a class
formation"** (NSW 8.1). `Skinner_Wiles_CFT_trick` and `global_class_field_theory` are
upstream-bead nodes even though they sit in the same bestiary section. Node 7 (local
duality) is the *lowest* PT-bead node any consumer touches; nothing in PT feeds back into
CFT.

## 5. Mathlib coverage (honest, checked in `.lake/packages/mathlib`, current pin)

- **Discrete group cohomology**: solid. `RepresentationTheory/Homological/GroupCohomology/`
  has `Basic`, `LowDegree` (explicit H⁰,H¹,H²), `LongExactSequence`, `Shapiro`,
  `Hilbert90`, `FiniteCyclic`, `Functoriality`; plus `GroupHomology/` and
  `TateCohomology/Basic`. **No cup products** anywhere in Mathlib RepresentationTheory.
- **Continuous cohomology**: exists and is recent (`ContCohomology/{Basic, Functoriality,
  LowDegree}`, authors Hill/Yang/Xie — copyright 2026). Defined via coinduced homogeneous
  cochains in `TopRep k G`. `LowDegree` currently proves **H⁰ = invariants only**; the
  file header's own TODO list: comparison with `groupCohomology` for discrete G, and the
  C(Gⁿ,M) description for locally compact G. No H¹-as-cocycles API, no LES, no
  inflation-restriction, no Shapiro in the continuous setting.
- **FLT-side extensions**: `FLT/Mathlib/.../ContCohomology/Basic.lean` (kernel/quotient
  models, `cohomologyIsoQuot`) and `CupProduct.lean` (`ContinuousCohomology.cup`) —
  active, marked destined for Mathlib.
- **Missing entirely in Mathlib**: Galois cohomology of local/global fields as such,
  H¹_nr, Brauer group beyond `Algebra/BrauerGroup/Defs.lean` (no Br(K_v) ≅ Q/Z, no Hasse
  invariant — grep confirms), class formations, any form of CFT (local CFT in progress
  externally via Lubin–Tate, bestiary:29), restricted products of cohomology,
  Selmer groups. `Topology/Algebra/PontryaginDual.lean` exists (basic duality only —
  usable for the finite-module duals PT needs).
- **FLT prerequisites present**: `Field.absoluteGaloisGroup` with functoriality/continuity
  (`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:39ff`).

## 6. Risks

1. **PT has no blueprint node** (bestiary:96 defers even the statement) — statement-design
   risk is live; the `modularity_lifting_theorem` `\uses` list undercounts (no global
   duality node exists to cite). Any cartography of the MLT proof must add edges the
   blueprint doesn't yet draw.
2. **Discrete ↔ continuous comparison unproven** in Mathlib; all of NSW's proofs run
   through direct limits over finite quotients, so node 1 blocks nodes 4–13 in practice.
3. **CFT input is the long pole**: node 6 (inv map) has no Mathlib Brauer-group theory
   behind it and depends on the external Lubin–Tate local CFT effort; timeline coupling
   to bead hub-lsb1u.9 is tight and one-directional.
4. **Topology of the nine-term sequence** (restricted products, strictness, Pontryagin
   duals of non-compact groups) is genuinely delicate and — per §2 — *unconsumed*;
   the main schedule risk is gold-plating node 11 when node 13 suffices.
5. Name-collision hazard for graders: Poitou appears in `Odlyzko.lean` for discriminant
   bounds; unrelated.
6. Project intent is to **axiomatize** node 13 short-term (`Assumptions/README.md:31,68`),
   so the proof-side S/M/L/XL numbers are not on the FLT critical path until the
   assumptions-discharge phase (post-2029 per README).

## 7. Size verdict

- Statement-only (the planned axiom, = what FLT needs by 2029): **M**, blocked mainly on
  continuous-H¹ API + local-fields glue; Livingston–Yang–Hill are on the critical piece.
- Weakest-sufficient proof package (nodes 1,3–10,12–14, skipping full 11): **XL** in
  aggregate, dominated by the two L-sized local theorems and the CFT import.
- Full NSW 8.6.10 nine-term topologized sequence: **XL+** and currently consumer-free;
  recommend explicitly descoping it to "derive middle-exactness only" unless Mathlib wants
  the general theorem for its own sake.
