# PT reconciled map — adversarial review (HYPOTHESIS STRENGTH + TRIVIALITY lens)
Reviewer: panel seat, hub-lsb1u.7.4. Target: origin/cartography/pt-reconciled @ pt-reconciled.md.

## Verdict: descope PROVISIONALLY ACCEPTED for the ready-now statement/axiom package
only; the "high confidence" ratings on nodes 11′/13/14 and the closure of Sha are
overstated. The evidentiary base is a `\notready` blueprint theorem
(`modularity_lifting_theorem`, ch04overview.tex:66) whose author states "we are very
far from even stating this theorem in Lean" and cites an uncertain literature proof
("I am not entirely sure where to find a proof of this... near-reference... assumes
a slightly stronger assumption"). Treating its `\uses` list as a complete dependency
audit — when the reconciled doc's own §2.1/§5.7 admits that list *undercounts* and
must be patched — is circular: absence of a global-duality edge in an admittedly
incomplete list is not evidence the dependency is absent.

## Vacuity traps (Q2 of the brief)
1. **Node 11′ cannot be typed without the machinery it claims to avoid.**
   Middle-exactness `H¹(G_S,M) → ⊕′_v H¹(G_v,M) → H¹(G_S,M*)^∨` requires a
   Pontryagin dual of the (non-compact, discrete) group `H¹(G_S,M*)` to even state the
   third arrow. The doc explicitly names "Pontryagin duals of non-compact groups" as
   part of the gold-plated NSW 8.6.10 content being *dropped*. You cannot keep 11′ and
   drop that dual construction — it's the same object. Either 11′ silently drags the
   dual-group machinery back in, or it will be typed with an ad hoc/incomplete
   surrogate, in which case "exactness" risks being provable vacuously (kernel=image
   trivially true if the third map is under-specified against a padded/topology-free
   codomain).
2. **Self-inconsistent node accounting.** Panel Q3 proposes axiomatizing the
   Greenberg–Wiles order formula directly (matching the README alias). If adopted,
   node 11′ is never actually formalized — middle-exactness is NSW-internal plumbing
   used only to *derive* 8.7.9 in the literature, not a Lean proof obligation once 13
   is taken as an axiom. Yet the merged table still counts 11′ inside "12 nodes in the
   descoped package," inflating the ready-now size claim with a node that does no
   formalization work under the doc's own preferred axiom shape.
3. Restricted-product topology risk as posed by the brief is real but secondary to #1:
   even granting a naive literal-direct-sum formulation of `⊕′_v`, the bigger failure
   mode is the undefined dual on the right, not the product on the left.

## Minimal / non-minimal ruling
The generic Selmer definition (ready-now item 5, `L=(L_v)` with `L_v=H¹_nr` a.e.) is
*structurally* adequate for both minimal and non-minimal deformation problems —
parametrizing by L covers both. But the claim that the **non-minimal case never
touches PT/Selmer** (because Skinner–Wiles/CFT absorbs all of it, per the ch04
proof sketch: SW-reduction to minimal, then plain TW-Kisin in the minimal case) rests
entirely on that same uncited, hedged proof sketch. Rate this MEDIUM confidence, not
the HIGH the table assigns nodes 13/14 — it is plausible, not verified. If Kisin-style
patching is ever used to handle non-minimal primes directly (rather than via SW
reduction first), a non-minimal Selmer-dimension comparison re-enters, which is closer
to Sha-adjacent territory than the reconciled doc admits.

## Panel questions — this lens's answers
1. **No** on outright ratification — accept only as a provisional, re-openable scope
   for the ready-now defs/axiom package; do not treat the local-only `\uses` list as
   confirmed complete until the auxiliary-prime/dual-Selmer-vanishing step is actually
   attempted in Lean (currently zero Selmer/H¹ content exists in FLT/Deformations or
   FLT/Patching — grepped, no hits beyond false positives).
2. No objection from this lens (orthogonal to hypothesis strength).
3. **Yes**, axiomatize the order formula directly — but say so explicitly and then
   *drop 11′ from the in-package node count* (see vacuity trap #2); don't have it both
   ways.
4. Convention choice (`M*` vs `M∨(1)`) directly affects whether 11′'s codomain matches
   the local pairing's codomain (item 3/node 7) — another reason 11′ is fragile, not
   "ready-now."
5. Agree to defer D1/D6a, but the doc's own confidence on D1 is "medium," the weakest
   entry in the table — the "if Mazur-discharge needs it, that's a new edge" framing
   reads as closed but is actually a live, unresolved contingency (per pass 1 §2.5)
   that could reopen Sha.
6. No objection from this lens.

File: /Users/kas/FLT/cartography/panel/pt-hypothesis.md (working tree only, not committed).
