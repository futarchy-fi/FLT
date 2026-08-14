# JL Dependency Honesty Panel — hub-lsb1u.4.4

Seat: adversarial (dependency honesty). Input: `cartography/jl-reconciled.md` (record only —
node-level detail lost to the 2026-08-14 disk incident), regenerated here from the two
canonical source maps (`origin/cartography/jacquet-langlands:cartography/jacquet-langlands.md`
= P1, `origin/cartography/jl-b:cartography-b/jl.md` = P2), against repo `origin/main` at
`e99f167`. Constraints from the reconciliation/adjudication: Route A (absorption) ratified;
pass-1 node 10 reassigned to bead .5; norm-factoring exclusion (P2 wins); Shimizu = default
deprecation target with trace formula kept as CBC-infra-sharing alternative; coefficient
bridge included (P2's N4, "missing from pass 1").

This regeneration is an independent reconstruction from the two source maps under the stated
constraints, not a recovered original — treat exact node boundaries as this panel's judgment
call, not as restored fact.

## Part 1 — Regenerated 13-node merged inventory

### Active assumption-phase (7)

| # | Node | Size | Confidence | Provenance | Repo state |
|---|---|---|---|---|---|
| 1 | Quaternion-algebra classification + finite-place rigidification (even-degree totally real `F`, discriminant-1 `D`) | M | High | P1 §1 (node 1); P2 §3 setup | **Done.** `FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean`, `FLT/QuaternionAlgebra/NumberField.lean:59-72`. |
| 2 | Quaternionic automorphic-form infrastructure (`S^D`, levels, characters, Hecke ops) | S | High | P2 N2 (both-pass: implicit substrate under P1 nodes 7,9) | **Done, sorry-free** except one `knownin1980s` (Voight 17.7.13 finiteness) at `Basic.lean:499`. |
| 3 | Petersson self-adjointness / Hecke eigenform decomposition | M | High | P2 N3; both-pass implicit prereq to P1 node 9 | **Mostly done.** `InnerProduct.lean:465` `isSymmetric_toModuleEnd_T`, `:619` `Eigenform.isInternal`. Zero `sorry` in the 920-line file. Sizing overstates remaining work — see Part 4. |
| 4 | Coefficient bridge: `ℂ ↔ ℚ̄_p` algebraicity of Hecke eigenvalues | M | Medium | P2 N4 only — **explicitly absent from P1**, included here per reconciliation instruction | **Not started.** No algebraicity/integrality lemma found for Hecke eigenvalues in the repo. |
| 5 | Level/Hecke compatibility bridge with norm-factoring (1-dim) exclusion | L | Medium | P1 node 7, corrected by P2 R3 (naive full-bijection claim is **false**) | **Partially done** — the trace/det matching machinery exists in `GaloisRep.IsAutomorphicOfLevel` (`Automorphic.lean:67-94`); the explicit norm-factoring exclusion is not yet encoded anywhere. |
| 6 | Hidden-content ledger inside absorbing axioms (.5 / .9 / .10) | S | High (mandatory, per adjudication rider 1) | New — synthesizes P1's "10 nodes collapse into one theorem" framing with P2 §2's "JL is hidden in `cyclic_base_change`" finding | **Not written.** `cyclic_base_change` (`Automorphic.lean:184`, `sorry`) carries no ledger comment today. |
| 7 | Non-blocking hedge draft: eigensystem-level standalone JL sketch (N2-only) | S | High (per adjudication rider 2) | P2 §3 route-minimal statement, reframed as a dormant-activation sketch rather than a live axiom | **Not written.** |

### Dormant Route-B (2)

| # | Node | Size | Confidence | Provenance | Repo state |
|---|---|---|---|---|---|
| 8 | Adelic `GL₂/F` weight-2 cusp forms / Hilbert modular forms (statement-only substrate) | L (XL if via general `(𝔤,K)`-modules) | Low-Medium | P2 N1 — "Route A skips N1 entirely"; blueprint's own bestiary calls it far off | Not started; explicitly out of scope while Route A holds. |
| 9 | Standalone JL statement + multiplicity-one/strong-mult-one statement, as terminal axioms | L | Low-Medium | Merges P2 N5+N6+N7+N8 with P1's route-minimal statement (§"Weakest sufficient statement") and nodes 2/3/8/9 | Needs node 8. Dormant unless the absorption boundary (node 6's axioms) fails to hold up under proof pressure. |

### Deprecation-phase XL (4)

| # | Node | Confidence | Provenance | Note |
|---|---|---|---|---|
| 10 | Local representation theory of `GL₂(F_v)` + local JL matching (principal series/Steinberg/discrete series, Whittaker↔Satake) | Low | P1 nodes 2+4; P2 N9 | Nothing in Mathlib. |
| 11 | Global multiplicity one / strong multiplicity one via Whittaker uniqueness | Low | P1 node 8; P2 N10 | Depends on node 10. |
| 12 | JL proof proper — **Shimizu theta-lift construction (default)** | Low | P2 N11 Shimizu branch — reconciliation's stated default; discriminant-1 case ≈ Eichler basis-problem | See Part 2: this default may be the *harder* infra bet, not the easier one. |
| 13 | JL proof proper — anisotropic trace formula (kept as **CBC-infra-sharing alternative**, not default) | Low | P1 nodes 5+6; P2 N11 trace-formula branch | Retained only because bead .5 (CBC) needs adjacent trace-formula machinery anyway. |

**13 = 7 + 2 + 4.** Node counts match the reconciliation record.

**Excluded by design:** P1's original node 10 ("JL-compatible cyclic base-change image
criterion") is not one of the 13 — per the reconciliation it is reassigned wholesale to bead
hub-lsb1u.5 and consumed there (see Part 3). It is not lost; it is downstream of nodes 6 and 9.

### Edges

Internal: `1→2`; `2→3`; `2,3→4` (see Part 2 for a challenge to this edge); `1,2→5`;
`5,6→` bead .5's axiom body; `8→9`; `9→` bead .5's paper-proof citation (Route B only);
`10→11`; `10→12` and `10→13` (both proof routes need local rep theory); `11→12,13` (mult-one
input to either proof route); `3→12` (Petersson comparison of inner products, P2's own
`N11 ← N9(+N3)` edge).

External: **.5 (CBC)** consumes nodes 5, 6, 9; **.9 (CFT)** consumes node 6 (automorphic
induction's citation content) and node 8 if Route B ever activates; **.10 (Galois reps)**
consumes nodes 5 and 6.

## Part 2 — Attack: hidden edges

1. **Petersson/semisimplicity is not the risk it looks like.** `isSymmetric_toModuleEnd_T`
   is already proven; simultaneous diagonalizability of a commuting family of self-adjoint
   operators on a finite-dim inner-product space is close to free (spectral theorem). The
   real hidden edge is elsewhere: the normalization lemmas (`haarQuot_mul_relIndex`,
   `sum_filter_map_eq_ΔIndex_div_ΔIndex`, lines 116-166) that make the inner product
   level-compatible are about *comparing* levels, not about ruling out oldform
   contamination — neither pass checks whether "multiplicity one within a fixed level"
   silently assumes newform/oldform separation that hasn't been formalized. Flag for .5:
   don't inherit multiplicity-one-per-eigenspace without checking this.

2. **Algebraicity (node 4) does not need CM theory — but both passes leave an edge
   underspecified.** Eigenvalue algebraicity here is a finite-dimensionality +
   lattice-stability argument (Hecke operators preserve an `𝒪_F`- or `ℤ_p`-lattice inside
   `S^D(U;ℂ)`), not a CM/complex-multiplication fact. The genuine hidden edge is
   **non-canonicity of the `ℂ ≅ ℚ̄_p` comparison isomorphism**: choosing one is required to
   even state node 4, it is not continuous/canonical, and neither map documents whether the
   Frobenius-trace matching in `Automorphic.lean:87-94` is invariant under the choice. This
   is a real gap, just not the one the prompt's "needs CM-theory" framing suggested.

3. **Theta-lift (Shimizu, node 12, the stated default) needs Weil-representation
   infrastructure that is more absent from Mathlib than trace-formula infrastructure is.**
   P2's own R5 says "no one has formalized any theta correspondence anywhere," but this
   was never wired into the edge list as a prerequisite. Shimizu's construction needs the
   Weil representation of a metaplectic/orthogonal-symplectic dual pair plus Siegel–Weil
   ingredients — exotic representation-theoretic machinery with zero Mathlib precedent,
   arguably a harder formalization bet than Arthur–Selberg trace-formula work (which at
   least has other formalization efforts elsewhere to borrow architecture from). **Panel
   question for adjudication: is "Shimizu = default because historically simpler" still
   the right call once judged by Mathlib-readiness rather than mathematical directness?**
   Recommend flagging this as open rather than settled, despite the reconciliation's phrasing.

4. **Local JL (node 10) quietly requires classifying admissible representations of
   `GL₂(F_v)` even to *state* what's being matched at split places**, not just at the
   division place. "The transfer is the identity at split places" (both passes) undersells
   this — you still need enough local Langlands/Satake theory at split `v` to know that
   "identity" is the right characterization and not just an assumption of convenience.

## Part 3 — Shared-node accounting vs CBC (.5) and Galois-reps (.10)

- **Node 6 (ledger) is genuinely shared** across .5's `cyclic_base_change` axiom and .9/.10's
  forthcoming automorphic-induction / Galois-rep-attachment axioms — tag
  `[shared:.5][shared:.9][shared:.10]`. Content differs per axiom (CBC's ledger enumerates
  JL-both-directions + M1 + M1′ + image classification; .10's enumerates the
  Carayol/Taylor-route JL use). **Double-count risk:** if this chapter budgets node 6 as one
  S-sized item *and* bead .5 separately budgets ledger-writing time inside its own bead
  costing, the same labor is counted twice. Resolution: this chapter (.4) owns drafting the
  shared ledger language/citations once; .5/.9/.10 each own only the mechanical insertion
  into their own axiom file. With that split, accounting is consistent.
- **Node 5 (level/Hecke bridge) is shared with .10**, tag `[shared:.10]` — it *is* the
  trace/det matching in `GaloisRep.IsAutomorphicOfLevel`, owned jointly by definition.
- **P1's reassigned node 10 is correctly excluded, not orphaned.** It is downstream of node 9
  (Route B) and of node 6/bead .5's own axiom (Route A) — a consumer, not an independent
  inventory item. No double-count found: it appears nowhere in the 13-node list and is named
  exactly once, in bead .5's scope.
- **Nodes 10-13 (deprecation XL) are NOT shared** — .5/.9/.10 consume only the *statement*
  (via nodes 5/6/9), never the eventual Lean *proof* of JL/mult-one. Correctly unshared.
- **Verdict: shared-node accounting is consistent** conditional on the node-6 single-owner
  split above being made explicit in bead costings — it is not automatic from the merged
  inventory alone, and should be stated as an explicit panel resolution, not assumed.

## Part 4 — Ready-now audit (6 candidates vs repo state)

1. **Quaternionic mult-one, N2-only statement** — confirmed absent (no such Lean statement
   found; P2's grep for "multiplicity" hit only unrelated ideal/Sylow uses). Ready now: yes,
   pure statement over existing `Eigenform`/`InnerProduct` infra, no new Mathlib deps.
   Highest-value claim holds up.
2. **Petersson semisimplicity lemmas** — **largely already shipped**
   (`isSymmetric_toModuleEnd_T`, `Eigenform.isInternal`, sorry-free file). Listed as a fresh
   ready-now item but most of the work is done; remaining scope is thin, not M-sized.
3. **Eigenvalue algebraicity** — confirmed not started, and harder than "ready now" implies:
   needs an explicit lattice-stability argument, not a one-sitting task despite M sizing.
4. **Ledger prose** — confirmed not written (`cyclic_base_change` has no ledger comment).
   Genuinely ready now, zero Lean risk, and blocking per adjudication rider 1 — should be
   sequenced first.
5. **Hedge JL sketch** — confirmed not written. Ready now, correctly marked non-blocking.
6. **`sorry` at `Automorphic.lean:100`** — confirmed present, but **misclassified**: it is
   `IsQuaternionAlgebra E (E ⊗[F] D) := sorry -- Ask Edison?`, a base-change-of-scalars
   instance for quaternion algebras, not JL content. It belongs to bead .5's or the
   quaternion-algebra miniproject's ready-now list, not this chapter's.

**Net: 3/6 candidates ready-now as described (#1, #4, #5); 1 overstated as remaining work
(#2, mostly done); 1 understated in difficulty (#3); 1 misattributed to the wrong chapter
(#6).**
