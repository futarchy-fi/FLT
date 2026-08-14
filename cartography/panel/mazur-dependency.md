# Mazur dependency panel — adversarial verdict

Lens: **dependency honesty**.  Evidence used: the reconciled map in
`/tmp/mazur-reconciled.md`, the read-only FLT checkout, and standard mathematical
dependencies.  I did not perform a literature lookup.  Any citation-sensitive
claim is marked `DEFER-TO-LITERATURE-SEAT` below.

## Executive verdict

The map is **DISHONEST-WITH-REPAIRS** as a dependency/readiness map (the
mathematical target W is sensible).  The principal defects are:

1. W is not enough to prove `FreyPackage.mazur`: the quotient branch needs the
   reducible-character/local-at-ell/Minkowski chain, an isogeny-on-torsion lemma,
   and the quotient construction.  Those are not W and are not wired in Lean.
2. Several “elementary” labels conceal Néron models, minimal models, finite-flat
   group schemes, fppf/étale cohomology, or analytic Euler-system input.
3. The closure grades for A1–A5, B1–B5, C1–C4, D7a/b, D8, D9, and W are lower
   than the closure they invoke.  D6a/b are correctly at XL+, but their edge
   lists are incomplete.
4. None of the five advertised ready-now nodes is proof-ready.  Four can have
   statement scaffolding now; A5 cannot even be honestly wired from W without
   additional bridge theorems.

The repository confirms the gap rather than closing it: `FLT/EllipticCurve/Torsion.lean`
has the cardinality and Galois-representation results as `sorry`,
`FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean` leaves the reduction theorem
as `sorry`, `FLT/GroupScheme/FiniteFlat.lean` is a plan/definition skeleton, and
`FLT/FreyCurve/Mazur.lean` still proves irreducibility with the universal
`knownin1980s`.  `Mazur_statement` is declared but, by repository search, has no
consumer.

## Closure rule used for grades

I distinguish a node's **local proof effort** from its **dependency-closure
grade**.  A statement can be S while its proof closure is XL+.  The map's grades
are retained in parentheses where useful; the grade after the arrow is the
honest closure grade for a proof in the present project.  `XL+` is the map's
largest grade; no claim of a new grade beyond that scale is intended.

## Node-by-node audit

### Part A — interface/glue

| Node | Hidden or missing dependency edges | Grade / status |
|---|---|---|
| A1 | Nagell–Lutz needs an integral/minimal Weierstrass model, discriminant and integrality/valuation lemmas.  The reduction proof instead needs good-prime existence, smooth group schemes, and the prime-to-residue-characteristic kernel/formal-group theorem (B1).  “Torsion is finite” is not obtained for free from `ncard`. | M → **L** (and **XL** if routed through B1); not proof-ready. |
| A2 | Division polynomials/separability, finite étale (E[n]), the Galois action and continuity, and the Weil pairing (hence determinant = cyclotomic and roots of unity) are all needed.  The current Torsion file explicitly leaves the main results as `sorry`. | L → **XL** in this repository; external Galois/elliptic and finite-flat edges required. |
| A3 | A quotient by a Galois-stable subgroup requires a finite-flat subgroup scheme, fppf quotient/representability, Cartier dual or Vélu construction, descent to Q, and the isogeny/dual-isogeny exact sequence on p-torsion.  A point-set quotient statement is insufficient. | L → **XL**; blueprint notready is accurate. |
| A4 | The group-theoretic injection of prime-to-ℓ torsion is easy only after A3 supplies a Q-isogeny and its Galois-equivariance.  “Three points survive” also needs the precise level-structure/moduli interpretation. | Local S, closure **XL**; statement may be frozen, proof is blocked by A3. |
| A5 | W only excludes a rational ℓ-point after full rational 2-torsion.  To derive irreducibility one additionally needs: reducible (E[ℓ]) ⇒ character semisimplification; unramifiedness away from ℓ and at 2; the finite-flat/ordinary-supersingular or Tate classification at ℓ; the global theorem that an everywhere-unramified character is trivial (Minkowski/class-field-theory edge); and the quotient/dual-isogeny bridge turning a trivial quotient into a trivial submodule on (E/C).  These are ch03/Frey-reduction results and are not wired. | M → **XL+**. **W alone is logically insufficient.** |

### Part B — elliptic-curve toolbox

| Node | Hidden or missing dependency edges | Grade / status |
|---|---|---|
| B1 | Minimal equations, smooth models, formal groups and the Néron–Ogg–Shafarevich direction are needed to prove injectivity of reduction on prime-to-q torsion.  The repo's good-reduction theorem is still `sorry`. | L → **XL**; not a small reduction lemma in the current API. |
| B2 | A per-curve 2-descent needs explicit models, isogeny/Selmer definitions, units and square classes in number fields, local solubility and a Mordell–Weil finite-generation/rank argument.  For the genus-2 case, rank 0 alone does not enumerate X(Q): one needs Abel–Jacobi, Jacobian torsion, and a rational-point/Mordell–Weil sieve (or Chabauty-type input).  The point-count sieve only bounds torsion; it does not certify rank 0. | M (per curve), L (genus 2) → **XL**; hidden number-field/class-group edges. |
| B3 | Frobenius trace/Hasse requires finite-field elliptic-curve theory and B1's specialization context.  It is conditional on the exact D8 route; finite enumeration over F2/F3 can replace the numerical Hasse bound only after the same reduction/model lemmas are proved. | L locally; closure **XL** and conditional pending PQ1. |
| B4 | Serre–Tate potentially-good reduction uses local Néron–Ogg–Shafarevich, inertia/potential good reduction and a trace comparison; it is not an elementary valuation lemma. | L → **XL**, conditional pending PQ1. |
| B5 | Tate uniformisation needs nonarchimedean analytic convergence, split/un-split twists, local Kummer/Hilbert 90, Galois cohomology, and (at ℓ) finite-flat extension results.  “Multiplicative reduction ⇒ cusp” additionally uses D2's integral modular curve, not Tate theory alone. | L → **XL**; B5 → D2 and finite-flat/cohomology edges must be explicit. |

### Part C — small primes

| Node | Hidden or missing dependency edges | Grade / status |
|---|---|---|
| C1 | The explicit X1(2,10) model must be tied to the coarse/fine level structure (including twists and cusps), then its elliptic rank, torsion and cusp list must be proved.  This uses D1 and B2, not just a named Kubert case. | L → **XL**; citation/model details `DEFER-TO-LITERATURE-SEAT`. |
| C2 | Same issue for X1(2,14): explicit birational maps, all rational points and cusp identification are additional theorems. | L → **XL**; `DEFER-TO-LITERATURE-SEAT`. |
| C3 | X1(11) rank 0 does not itself say which torsion points are cusps.  One needs the model, Mordell–Weil torsion computation and modular cusp identification. | M → **L/XL**; `DEFER-TO-LITERATURE-SEAT`. |
| C4 | The genus-2 Jacobian rank-0 descent is only an intermediate result.  Rational-point determination, the Abel–Jacobi embedding and the complete cusp list are separate dependencies. | L → **XL+**; `DEFER-TO-LITERATURE-SEAT`. |
| C5 | Ogg/Kubert's alleged explicit 17 and 19 arguments were not checked.  Do not treat this as a cheapening or alter the D-core threshold. | M–L provisional; **DEFER-TO-LITERATURE-SEAT** and low confidence. |

### Part D — modular-Jacobian core

| Node | Hidden or missing dependency edges | Grade / status |
|---|---|---|
| D1 | Deligne–Rapoport/Katz–Mazur stacks/coarse moduli, rigidification at elliptic points, compactification, cusp fields/widths, twists, and the precise X1-to-X0 moduli map are needed.  Atkin–Lehner over Q is another theorem, not a definitional fact. | XL → **XL+** (at least for a Lean proof). |
| D2 | The integral model needs generalized elliptic curves, Drinfeld/finite-flat level structures, compactification and q-expansion principles.  “v_q(j)<0 catches a cusp” also needs B5 and a theorem identifying the model's boundary, not merely a smooth-over-Z[1/ℓ] model. | XL → **XL+**. |
| D3 | Existence of the Jacobian/Picard scheme, Riemann–Roch, divisor classes, a rational cusp base point, and functorial Abel–Jacobi maps are all hidden. | XL → **XL+**. |
| D4 | Néron models, component groups/formal groups, the Néron mapping property, extension of rational points to sections, and the exact prime-to-q specialization statement (especially at 2) are needed. | XL → **XL+**. |
| D5 | Algebraic/analytic cusp forms, q-expansions, Hecke correspondences, Cotangent ≅ S2, Eichler–Shimura, and smooth-proper/etale base change are required.  The repo's quaternionic Hecke API is not this classical J0(ℓ) theory. | XL → **XL+**; explicit Hecke/etale-cohomology chapter edge missing. |
| D6a | In addition to D1–D5: Eisenstein ideal and cuspidal subgroup arithmetic, Raynaud classification, Cartier duality, finite-flat/fppf cohomology, local Kummer theory, global class-field/class-group input and (for Selmer-style formulations) Poitou–Tate/global duality. | XL+ (reasonable local grade), but **edge list incomplete**. |
| D6b | Winding quotient requires modular symbols/winding homomorphism, analytic (L)-functions and a nonvanishing/rank-0 theorem.  MW rank 0 imports Gross–Zagier + Kolyvagin–Logachev or Kato, Euler systems, Selmer/Galois cohomology and Poitou–Tate; class-field input is not optional bookkeeping. | XL+ (reasonable), with a much larger external analytic/cohomological closure than advertised. |
| D7a | The algebraic implication is elementary on paper, but the stated geometric criterion needs completed local rings, cotangent spaces and scheme-theoretic formal neighbourhoods.  A repository search found no completed-local/formal-immersion API. | S/M → **L** in the current formalization; statement-only bead, not proof-ready. |
| D7b | Application requires D1–D5, D7a, q-expansion at the chosen cusp, Hecke-stable cotangent injection, and proof that the relevant a1 survives in the chosen quotient in characteristics 2 or 3. | L–XL → **XL+**. |
| D8 | Besides D1–D7, one needs the exact special-fibre/Néron argument, a finite-Mordell–Weil (not merely rank-0) quotient, torsion specialization and annihilation, cusp residue fields, and extension/cusp-swapping for the Atkin–Lehner involution.  The displayed route silently uses D6 → D8. | L → **XL+**; exact formulation `DEFER-TO-LITERATURE-SEAT` (PQ1). |
| D9 | This is not M-grade glue in a dependency-honest proof: it consumes the complete D-core and its integral-model, Hecke, Néron and formal-immersion stack. | M → **XL+**. |
| W | The assembly is syntactically easy, but its proof closure is C1–C4 + D9 plus A5's ch03 bridge if it is used to replace Mazur's axiom. | S locally → **XL+**; do not advertise W as shovel-ready proof. |

## Missing external-chapter edges

The union claim in the map is therefore false as an edge-completeness claim.  At
minimum add these named edges:

* **Elliptic/reduction:** minimal integral Weierstrass models; formal groups and
  Néron models; the good-reduction/Néron–Ogg–Shafarevich theorem; Tate
  uniformisation and local Kummer/Hilbert 90; Weil pairing and cyclotomic
  representations.
* **Frey/ch03 Galois representations:** `FreyCurve.torsion_isHardlyRamified`,
  local finite-flat classification at ℓ (ordinary versus supersingular), Tate
  analysis at 2, semisimplification/Brauer–Nesbitt bookkeeping, the
  everywhere-unramified-character ⇒ trivial theorem (Minkowski or global class
  field theory), and the dual-isogeny map on ℓ-torsion.  These are mandatory for
  A5 and are not represented by a W edge.
* **Number-field arithmetic:** explicit class groups, units, square classes,
  local-global solubility, 2-Selmer groups and Mordell–Weil finite generation for
  B2/C1–C4.  “Rank 0” and “cusps only” are different nodes.
* **Modular-curve geometry:** stacks/coarse rigidification, generalized elliptic
  curves, Deligne–Rapoport/Katz–Mazur integral models, cusp fields and widths,
  Atkin–Lehner extension, Jacobians/Picard/Riemann–Roch and Abel–Jacobi.
* **Hecke/cohomology:** classical Hecke correspondences, q-expansion principle,
  Eichler–Shimura, and etale cohomology/base-change.  The existing quaternionic
  Hecke files do not discharge D5.
* **Global duality:** fppf/flat and Galois cohomology, local/global class field
  theory, Selmer conditions and Poitou–Tate.  These are explicit D6a/D6b edges,
  and are also latent in 2-descent if it is done honestly.
* **Analytic route:** modular symbols/winding, (L)-functions, Gross–Zagier,
  Kolyvagin–Logachev or Kato, Euler systems and analytic-to-algebraic rank.

No Poitou–Tate theorem is needed merely to state W, but it is a genuine hidden
edge of the winding/Eisenstein Selmer proofs and of any nontrivial descent
formalization.  No Galois-representation chapter can be treated as a black box
for A5: the ch03 bridge is the critical consumer.

## Audit of the five “ready-now” nodes

| Advertised bead | Verdict | Minimum honest repair |
|---|---|---|
| **A5 wiring** | **Not unblocked.** W does not imply irreducibility; the character, local finite-flat/Tate, Minkowski and quotient/dual-isogeny bridge is absent, and the current theorem is `knownin1980s`. | Add explicit intermediate assumptions/theorems (`reducible_structure`, local character lemma, quotient-on-torsion), then wire W. Coordinate PQ7 before deleting the old axiom. |
| **D7a formal-immersion criterion** | **Statement-only.** The proposed geometric statement has no completed-local/cotangent API in the checked tree. | First define the ring-theoretic lemma in existing algebra, or build the missing completion/cotangent infrastructure and prove the scheme version. |
| **A4 2-torsion survives** | **Statement-only.** Its proof waits on A3's quotient and prime-to-ℓ isogeny facts. | Freeze a precise theorem, including the Galois-equivariant isogeny and images of all three nonzero 2-torsion points. |
| **A1 torsion finiteness** | **Statement-only.** Nagell–Lutz/minimal-model or B1 reduction machinery is not present as a completed proof. | Choose one route and expose its integral-model/formal-group prerequisites; do not call it proof-ready merely because it is classical. |
| **Explicit small-curve plane models** | **Statement-only.** Equations can be recorded, but modular interpretation, birational equivalence, rank/torsion descent and cusp enumeration remain blocked by D1/B2 and literature citations. | Freeze models with a separate “rational points = cusps” theorem and a declared literature/descent dependency. |

Thus **0/5** are genuinely unblocked proofs; **4/5** are useful statement/API
scaffolds, while A5 needs additional interface assumptions even for an honest
wiring bead.

## Panel questions (dependency-honesty answers)

### PQ1 — D8 endgame

**DEFER-TO-LITERATURE-SEAT** for the exact Mazur 1977 Theorem 8/Snowden line
references, the special fibre chosen at 2 versus 3, and the precise role of
the Atkin–Lehner involution.  The dependency audit says the following must be made explicit before
freezing Lean statements: prime-to-2 torsion specialization (so the char-2
kernel issue is harmless for ℓ≥17), the good-reduction finite-field count,
the multiplicative/Tate-to-cusp implication, cusp swapping, and a torsion-killing
argument in the rank-0 quotient.  Finite enumeration over F2/F3 may replace a
Hasse inequality only after those model and specialization
lemmas exist.  The λ=1 trace variant is not accepted as an equivalent route:
it needs a good/potentially-good trace theorem and can silently apply a good-
reduction trace formula at additive reduction; the alleged a3=4 boundary
cannot be settled here.  Keep it as an unverified alternative.

### PQ2 — Eisenstein versus winding

Neither prong is simple or unblocked.  The winding route is dependency-dishonest
if described as merely “a simpler quotient”: its rank-0 step imports analytic
nonvanishing plus Gross–Zagier/Kolyvagin–Logachev (or Kato), Euler systems and
global duality.  Eisenstein descent has the more explicit algebraic stack and
reuses finite-flat/flat-cohomology infrastructure needed elsewhere in FLT,
although it also needs class-field/global-duality input.  For dependency
honesty I recommend an Eisenstein paper-audit spike first, with both routes
labelled XL+ until that audit is complete; this is not a claim that Eisenstein
will be cheaper.  Do not start Part-D formalization on the word “winding”.

### PQ3 — ℓ = 17, 19 classical?

**DEFER-TO-LITERATURE-SEAT.** The Ogg/Kubert attribution and the exact rational-
point arguments were not checked.  Until then C5 remains low confidence and the
D-core conservatively starts at ℓ≥17.  Even a positive answer changes milestone
ordering, not the hidden D1–D8 closure.

### PQ4 — exponent re-basing

Keep the full W interface provisionally.  Citing the FLT-regular Lean project is
an unlisted external dependency with an interface/quantifier obligation: it must
state exactly whether it handles every regular prime, how a counterexample is
re-based, and whether its cyclotomic class-group machinery is importable.  The
first irregular prime is not a substitute for proving the required parameterized
statement.  Only after that contract is accepted may the top-level branch remove
the regular cases (including 5, 7, 11 and 13); do not describe this as simply
“leave the D-core” without changing W's quantifiers to the remaining exponents.

### PQ5 — citations

Every citation listed in PQ5 is **DEFER-TO-LITERATURE-SEAT** here: Serre Duke
Prop. 6; Silverman AEC VII.3.1; Mazur 1977 Theorems 4/8 and II.9–10;
Serre–Tate Theorem 2; Kubert, Billing–Mahler, Mazur–Tate; the conductor/genus
identifications; and Katz's appendix.  No Lean statement should be frozen as a
direct transcription of those claims until the literature seat records the exact
hypotheses and conclusion.

### PQ6 — integral-model sizing

An ad hoc smooth-over-ℚ[1/ℓ] model is not an honest cheap replacement for
Deligne–Rapoport/Katz–Mazur: the cusp boundary, generalized elliptic curves,
finite-flat level structures, q-expansion and the “potentially multiplicative
means cusp” lemma are precisely the parts it would have to re-prove.  A reduced
model can be used only if those consequences are separately imported as named
theorems/axioms.  Make the noncircular edge **D1(coarse generic moduli) →
D2(integral compactification)** explicit; D2 must not be used to define D1.
Full-model and ad-hoc sizing are both literature-dependent here:
**DEFER-TO-LITERATURE-SEAT** for the exact minimal theorem package.

### PQ7 — replacing `Mazur_statement`

The dead-code finding is confirmed (`rg` finds only the declaration), but removal
still needs an upstream-safe protocol:

1. Add a namespaced W axiom/interface with its exact small-ℓ and ℓ≥11 clauses,
   and separately state torsion finiteness if any `ncard` consumer needs it.
2. Add and prove (or explicitly assume) the ch03 reducible-structure,
   local-character and quotient/dual-isogeny bridges; W by itself is not the
   replacement proof.
3. Re-prove `FreyPackage.mazur` from those bridges and W, update blueprint
   `uses`, and remove the `knownin1980s` invocation.
4. Run a repository-wide consumer/axiom scan and CI with the old axiom retained
   as a temporary compatibility alias; only then delete or deprecate it in
   coordination with KMB/upstream.

The protocol decision is therefore **not ready for deletion**, even though the
old axiom itself is unused.

## Required repairs before an HONEST verdict

1. Replace the union edge claim with the explicit external edges above, especially
   A5 ← ch03 and D6a/b → global duality/class field theory.
2. Split every “rank 0”, “cusps only”, “formal immersion” and “torsion finite”
   statement into the intermediate lemmas it actually consumes.
3. Re-grade by closure: A2/A3/B1/B5/C1–C4/D1–D5/D7b/D8/D9/W are XL or XL+;
   A1 and D7a are at least L in the present API; A5 is XL+.
4. Mark PQ1, PQ3, PQ5 and the model-size portion of PQ6 as
   `DEFER-TO-LITERATURE-SEAT`, and do not use C5 or the λ=1 route for planning.
5. Reclassify the five ready-now beads as statement scaffolds, not unblocked
   proofs, until the named interfaces land.

**Overall: DISHONEST-WITH-REPAIRS.** The hidden-edge count is substantial but
repairable; the honest campaign boundary is W as a carefully specified interface,
with the entire proof closure (and especially the A5 ch03 bridge) exposed rather
than silently credited to “Mazur”.
