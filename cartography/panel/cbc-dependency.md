# CBC chapter — panel seat: dependency honesty + ledger audit (hub-lsb1u.5.5)

Seat: adversarial (dependency honesty / ledger audit). Input:
`origin/cartography/cbc-reconciled:cartography/cbc-reconciled.md` (D-1..D-8
ledger, S1-S8 statement inventory), cross-checked against `panel/jl` (JL's
regenerated 13-node inventory + adjudication, hub-lsb1u.4.4) and `panel/cft`
(CFT adjudication, hub-lsb1u.9.5), against repo state at `origin/main`
(`e99f167`). Default skeptical.

## 1. Ledger completeness: INCOMPLETE — one real gap (D-9 candidate), one non-gap

**Not a gap: AI-quad proof debt.** D-7 already exists ("AI-quad proof:
theta-series/Weil-representation or converse-theorem construction of
`AI_{K/F}(χ)`... Owner: CBC, consumed by hub-lsb1u.9", size L-XL) and pairs
correctly with statement node S6. JL's own adjudication (H1: "automorphic
induction is ORPHANED... assignment: the CBC chapter owns it, its reconciled
map already scopes AI to the quadratic-CM case as **node S4**") is factually
wrong about the node label — CBC's AI-quad statement is **S6**, not S4 (S4 is
the descent statement). This is a cross-chapter citation error on JL's side,
not a CBC ledger hole, but it should be corrected in JL's adjudication record
since a future reader will grep for "S4" and land on the wrong node.

**Real gap: D-9 needed for the U₁(S,Q) level hole (JL's H2).** JL's
adjudication (H2) found `IsAutomorphicOfLevel` hardcodes `Q = ∅`, so
`cyclic_base_change` never quantifies over the TW-augmented levels R=T
patching consumes — "BLOCKS axiom pinning until either the level structure is
generalized over Q or the restriction is proven sufficient." This bears
directly on CBC's own core interface (S3's level bound, S5's derivation of
`cyclic_base_change`) and is untracked anywhere in D-1..D-8. Recommend
**D-9: generalize (or prove sufficiency of) the `Q = ∅` restriction in
`IsAutomorphicOfLevel`/`cyclic_base_change` against TW-augmented levels
consumed by R=T patching.** Owner: CBC (interface holder), size unclear
pending literature-verify — flag as open, not M by default.

**Chebotarev/density leak: CONFIRMED, and currently mispriced.** CFT's
adjudication (repair #2) found the existence-only Skinner–Wiles route needs
Chebotarev/Dirichlet-density input that "exists NOWHERE (Mathlib, FLT,
blueprint — zero hits)" and had to add it as a brand-new, previously
invisible node to the CFT chapter. This is exactly CBC's **S7**
("Skinner–Wiles CFT trick edge... Owned by CFT hub-lsb1u.10; CBC consumes"),
priced in cbc-reconciled.md at "M (given GCFT)". That sizing predates CFT's
discovery and silently assumed the density input was already inside "GCFT" —
it is not. S7's true cost is at minimum the CFT chapter's new node cost,
which CFT itself has not yet finished grading (see CFT's own boundary-
repricing repair for node 8/D2, "XL-adjacent"). **S7 must be repriced,
provisionally to L, pending CFT's number**, and a one-line cross-reference to
CFT's new node added so the same density-construction labor isn't graded
twice under two names. S8 (Chebotarev + `compatible_family` for
`ρ_{BC(π)} ≅ ρ_π|_{G_E}`) is a *different* Chebotarev use — comparing
Frobenius traces outside a finite set, standard density-theorem territory,
not the existence-construction route CFT flagged as absent — so S8's M
grade is not directly hit by the same finding, but the panel should not
assume it for free either; no repo evidence either way was found this pass.

## 2. Shared-node accounting vs JL

Consistent, with the S4/S6 mislabeling above as the one correction needed.
JL's own accounting (Part 3 of jl-dependency.md) is internally sound: node 6
(shared ledger prose) is single-owned by JL-chapter drafting + mechanical
insertion by consumers; node 5 (level/Hecke bridge) tagged `[shared:.10]`
only, not CBC; JL's deprecation-XL nodes 10-13 (local rep theory, mult-one,
JL proof proper) are correctly *not* shared with CBC's ledger — CBC's D-1
through D-5 cite the same trace-formula/local-GL2/mult-one material but as
CBC's *cyclic-twisted* increment, with JL/hub-lsb1u.4 as owner for the
shared infra (D-3, D-4, mult-one part of D-5) — matches JL's framing. No
double-count found beyond the S4/S6 citation slip.

## 3. S1 grade verdict: STALE-CONSERVATIVE, not dishonest, but should drop

Repo check: `FLT/AutomorphicForm/QuaternionAlgebra/{Basic,InnerProduct,
FiniteDimensional}.lean` and `HeckeOperators/{Abstract,Local,Concrete}.lean`
are **0 `sorry`** each; `FLT/QuaternionAlgebra/NumberField.lean` is 0 `sorry`.
The only blemish is one `knownin1980s` marker at `Basic.lean:499` (Voight
17.7.13 finiteness) — matches JL panel's node-1/node-2 "Done" grades exactly.
`FLT/GaloisRepresentation/Automorphic.lean` carries 2 `sorry`s (`:100`
base-change-of-scalars instance — JL's adjudication reassigns this to CBC/
quaternion-algebra scope, correctly, not S1 content; `:184` the
`cyclic_base_change` conclusion itself, downstream of S1 not part of it).
Verdict: **S1's "M, high confidence, dominates statement cost" framing
overstates remaining work.** The substrate it names is already sorry-free
modulo one axiom marker; JL's own panel flagged the same over-grading on its
mirror node (node 3, "sizing overstates remaining work"). CBC's ledger should
either drop S1 to S or add an explicit note crediting the JL-side build-out,
matching JL's regenerated inventory rather than treating S1 as a fresh cost.

## 4. Ready-now audit (6 candidates, cbc-reconciled §7)

1. S2 (norm on Satake data) — no blocking dependency found; algebra-only
   against a stub type. Holds up.
2. S5 gluing skeleton — Mathlib `IsSolvable`/chief-series infra exists per
   cited file; holds up as statable now, *un*-repriced by the H2/D-9 finding
   above only insofar as S5 derives `cyclic_base_change` itself, which is
   the object H2 says is presently mis-scoped on `Q`. Statable now, but the
   ledger comment should note the D-9 dependency so it isn't quietly frozen
   as final once stated.
3. S3/S4 as assumption statements — confirmed blocked only on S1 (which per
   §3 above is nearly done, so this candidate is *more* ready than the
   reconciled map credits, not less).
4. S6 (AI-quad) — confirmed independent of S3/S4; JL's H1 finding (nothing
   carries AI content in Lean yet) corroborates "not started," consistent.
5. S8 Chebotarev comparison lemma — statable now against `compatible_family`;
   no evidence found that this route shares CFT's absent-density problem
   (see §1). Holds up.
6. `cyclic_base_change` docstring/ledger sharpening — still correct and now
   has more to record: fold in D-9 (H2) and the S7 repricing (§1) as new TODO
   lines, not just D3's level-bound reading.

## File

`/Users/kas/FLT/cartography/panel/cbc-dependency.md` (working tree only, not
committed).
