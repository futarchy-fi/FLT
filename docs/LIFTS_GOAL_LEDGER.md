# GOAL-L0: lifting for the positive-natural FLT goal

This is a delta to [LF0](LIFT_FAMILY_PLAN.md), especially its restricted lifting
contract and K1, and [CORE](CORE_PLAN.md), L0–L6. It does not replace those plans
or their shared lifting/family budget. Queue IDs below are **GL**, not their L IDs.

## Checked baseline and admission

At task start, checked 2026-09-30 UTC: HEAD = GitHub `main` =
`c557fcd66261f7de888076c086a7eb28df6539af`; `origin/main` agrees.
The local branch named `main` is older; it is not the audited baseline.
Checks: `git rev-parse HEAD origin/main`; `gh api repos/futarchy-fi/FLT/commits/main --jq .sha`.
Mathlib: `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
All file:line references and readiness claims below refer to this snapshot.
Freshness checked 18:26:35 UTC: main advanced to `d4e575010ee5015026d7afa23ac17eb0ceac4700`;
only `docs/MAZUR_GOAL_LEDGER.md` changed, so the audited Lean sources still match main.
Evidence: `gh api repos/futarchy-fi/FLT/compare/c557fcd66261f7de888076c086a7eb28df6539af...d4e575010ee5015026d7afa23ac17eb0ceac4700 --jq '[.files[].filename]'`.

The exact admitted declaration is `GaloisRepresentation.IsHardlyRamified.lifts`,
`FLT/GaloisRepresentation/HardlyRamified/Lift.lean:37` (body `sorry`, line 48).
Its full context and result, with only whitespace changed, are:

```lean
namespace GaloisRepresentation.IsHardlyRamified
universe u v
variable {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V] (hV : Module.rank k V = 2)
open TensorProduct
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry
end GaloisRepresentation.IsHardlyRamified
```

Consumer: `FLT/Assembly/ExistingInputs.lean:31` proves `hardlyRamifiedLifting`
by applying this admission at line 33. `FermatsLastTheorem.lean:19` supplies
that adapter at line 24 to `PNat.pow_add_pow_ne_pow_of_three_inputs`
(`FLT/Assembly/ThreeInputFinal.lean:24`). The actual call to the lifting input
is `FLT/Assembly/PrimeField.lean:48`, through `FLT/Assembly/Proof.lean:27`.
The generic `HardlyRamified/PrimeField.lean:53` is a separate caller.

Build checked 2026-09-30 18:21:14 UTC: `LEAN_NUM_THREADS=2 lake build FermatsLastTheorem`
(foreground; `Scratch/lifts-goal-build.log`), exit 0, 10,293 targets.
Audit command (foreground, from this baseline):
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsGoalAudit.lean > Scratch/lifts-goal-audit.log 2>&1`.
The scratch file imports `FermatsLastTheorem` and `Lean`, prints axioms of the
final theorem, `lifts`, and its adapter, then runs the type-and-body constant
walker from the prior GOAL-AUDIT on the final theorem and adapter. It rejects
missing constants and compares its axiom set with Lean's `collectAxioms`.
Checked 2026-09-30 18:32:32 UTC: exit 0; final root 133,419 declarations,
zero missing, axiom set `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
The lifting adapter visits 43,935 declarations, zero missing; its only library
frontier is `lifts` at line 37. Both `lifts` and its adapter have exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`. The legacy `three_adic`
is not reachable from the final goal. Both walks agree with `collectAxioms`.
Scratch is local evidence, deliberately not committed; a minimal independent
rerun is a scratch file containing `import FermatsLastTheorem` and
`#print axioms PNat.pow_add_pow_ne_pow` / `#print axioms FLT.Assembly.hardlyRamifiedLifting`.
The other arithmetic inputs remain `mem_isCompatible` and `Mazur_statement`;
this ledger does not propose proving them as lifting leaves.

## Smallest retained lifting boundary and source ledger

Use **exactly `FreyLifting` and `HasPrimeFieldLift` from LF0's “Restricted
lifting contract”**, not a new interchangeable existential. Thus: `P : FreyPackage`,
`17 ≤ P.p`, canonical `PadicInt.toZMod`, residual `P.freyCurve.galoisRep P.p P.hppos`,
and its irreducibility imply the existential above specialized to `k = ZMod P.p`
and `Type`, with its *same* residual conjugacy. HR is already proved by
`HardlyRamified/Frey.lean:95`. `Proof.lean:57` needs only these Frey inputs;
`Assembly/Proof.lean:30` currently discards the ≥17 bound and must later be rewired.
This is the weakest retained **lifting interface**, not a logically least
sufficient proposition: LF0's `FreyResidualTraceInput` is the weaker endgame
consequence, but combines lifting, companions and three-adic arithmetic.
No arbitrary finite fields, p=3 case or universes are needed for this goal.

Sources checked directly: Khare–Wintenberger, *Serre's modularity conjecture I*,
Invent. Math. 178 (2009), 485–504 ([author manuscript](https://www.math.ucla.edu/~shekhar/papers/results.pdf), **I**);
and *II*, ibid. 505–586, DOI 10.1007/s00222-009-0206-6
([author manuscript](https://www.math.ucla.edu/~shekhar/papers/proofs.pdf), **II**).
The numbering below is the downloaded author manuscripts (23 and 98 pages),
not an assertion that journal pagination matches. Downloads and extracted text:
`Scratch/kw-{results,proofs}.{pdf,txt}`, checked 2026-09-30.

| Step / source | Exact hypothesis obligation or delta |
|---|---|
| Residual oddness and absolute irreducibility; I §4 (definition of odd), II Theorem 6.1 (S-type input) | Already proved in `HardlyRamified/AbsoluteIrreducibility.lean:68,99`, using `RationalComplexConjugation.lean:75`. Do not redispatch CORE L0. GL2 only exposes the determinant equality. |
| Finite-flat residual input has Serre weight 2; II Proposition 3.6 and §3.2.2 (low-weight crystalline local problem); Serre, *Sur les représentations modulaires de degré 2*, Duke 54 (1987), §2 (weight definition) | For the discrete prime field, specialize `IsFlatAt.cond` to the zero ideal (`Deformations/RepresentationTheory/GaloisRep.lean:396`), transport through the quotient/tensor identity, then identify the resulting finite-flat model with Serre's weight-2 condition. II §3.2.2 explicitly uses finite flatness to select weight 2. A fully matched Lean dictionary, including the reverse integral assertion for the lift, remains a design gate; Proposition 3.6 alone is not that dictionary. |
| Cyclotomic-restriction absolute irreducibility; I Lemma 6.2(ii) | Over the algebraic closure, reducible restriction forces weight `(p+1)/2` or `(p+3)/2`; weight 2 and p≥17 exclude both. First prove the weight dictionary. Never add this restriction as a premise of `FreyLifting`, nor require an unproved “large image” assumption. |
| Fixed determinant and local rings; II Theorem 3.1, Proposition 3.6, §3.3.4 | Choose ψ=1, hence determinant χp; S={2,p,∞}. At p use weight-2 crystalline; at 2 use the fixed-character semistable type of §3.3.4; elsewhere impose unramifiedness. Need integral finite-flatness at **every open coefficient quotient**, not just Hodge–Tate weights. |
| Exact local type at 2; II Theorem 3.1 and §3.3.4 (twist of semistable deformations) | Use the residual quotient δ from `Defs.lean:115`, lift it to a fixed unramified quadratic γ, and impose upper-triangular type `(γχp, γ)` even when the residual representation is unramified at 2. The source imposes γ²χp=φ, hence γ²=1 for φ=χp. Recovering the **surjective integral quotient** over the chosen coefficient order remains a bridge; minimal/unramified deformation or inertia trace 2 alone does not fix Frobenius eigenvalues. |
| Global deformation dimension; II Proposition 4.5 | Prove the arithmetic Selmer presentation and dimension ≥1 for these local rings. Existing `Deformations/Representable.lean:38` is unrestricted; line 114 is admitted and is not an input to reuse as proved. |
| Residual modular seed, comparison and finiteness; II Theorems 6.1, 8.2, 10.1; Proposition 9.2 | Theorem 10.1 gives finite Zp-module global ring after these hypotheses. Construct the totally real auxiliary fields with the local/disjointness properties used in its proof. This is not potential modularity of an already-assumed desired global lift. |
| Characteristic-zero point; II Corollary 4.7, §10.3.1 | Dimension plus finiteness makes p nonnilpotent. Extract a prime avoiding p, then a finite characteristic-zero coefficient domain; GL3 is only the prime-extraction sublemma. Abstract representability or finiteness alone is insufficient. |
| Integral coefficients and residual identification; II Corollary 4.7 and I Theorem 5.1(1) | An O′-valued point may enlarge the residue field. Preserve the original residual Fp model via the finite local image/order of the deformation ring, with residue Fp, or prove coefficient descent. Taking O′ itself does **not** automatically give `Algebra O′ (ZMod p)`. Prove freeness, module topology, continuity, HR and the actual tensor-conjugacy witness over that order. |

Use **II Theorem 10.1 + Corollary 4.7 with §3.3.4 at 2** as the lifting
source. I Theorem 5.1(1) alone is insufficient: a minimal unramified lift at 2
need not have the required quadratic quotient. This sharpens LF0 K1. The unresolved weight/local-integral dictionaries
above are explicit gates; this ledger does not certify a complete matched proof.
Do not obtain an auxiliary-ramified lift and silently call it hardly ramified.
Compatible-family source/hypothesis work stays in LF0; no duplicate queue here.

## Ordered dispatch queue

All paths below are **new proposed modules**, under `FLT/GaloisRepresentation/HardlyRamified/`.
Caps include headers/imports/proofs. GL1–GL3 are independently ready; they prove
small algebraic facts, not existence of lifts. No library edits were made by L0.

**GL1 — `PrimeResidueMap.lean`, cap 180, READY; no queue dependencies.**
Import `Mathlib.NumberTheory.Padics.RingHoms`. Exact statement:
```lean
theorem primeResidueMap_unique (p : ℕ) [Fact p.Prime]
    (f : ℤ_[p] →+* ZMod p) : f = PadicInt.toZMod
```
Use `PadicInt.toZMod_spec` to subtract the canonical integer representative;
the difference lies in `(p)`, killed by f. This fixes the coefficient map in
residual deformation interfaces without assuming continuity or a second algebra.
Anchors: `Padics/RingHoms.lean:318,327,442`,
`Padics/PadicIntegers.lean:513` (`maximalIdeal_eq_span_p`).
For the final cast, change the target to `f x = (x.zmodRepr : ZMod p)`.
Do not reimplement the existing `PadicInt.residueField` equivalence.

**GL2 — `ResidualOddness.lean`, cap 120, READY; no queue dependencies.**
Import `HardlyRamified.AbsoluteIrreducibility`. In its exact variable context
(`AbsoluteIrreducibility.lean:61–65`, also `[Module.Free k V]`), prove:
```lean
theorem det_complexConjugation (hρ : IsHardlyRamified hpodd hV ρ) :
    ρ.det ThreeAdicPlan.rationalComplexConjugation = -1
```
Proof: specialize `hρ.det`, rewrite `rationalComplexConjugation_cyclotomic`,
`map_neg`, `map_one`. Consumer: the oddness field of the source's residual seed.
Reuse `hρ.isAbsolutelyIrreducible` separately; do not prove it again.

**GL3 — `LiftPrimeAvoidingP.lean`, cap 100, READY; no queue dependencies.**
Import `Mathlib.RingTheory.Nilpotent.Lemmas`. Exact statement:
```lean
theorem exists_prime_avoiding_p (D : Type) [CommRing D] (p : ℕ)
    (h : ¬ IsNilpotent (p : D)) :
    ∃ P : Ideal D, P.IsPrime ∧ (p : D) ∉ P
```
Use `nilpotent_iff_mem_prime` (that file:59) and classical negation.
Source: II Corollary 4.7; Atiyah–Macdonald, *Introduction to Commutative Algebra*,
Proposition 1.8. Its nonnilpotence premise remains the arithmetic ring construction's obligation.

**GL4 — `LiftDomainFree.lean`, cap 300, READY after GL3; algebra only.**
Import `HardlyRamified.B5Inputs` for the existing quotient/PID infrastructure.
With `(p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [Algebra ℤ_[p] D]`
and `[Module.Finite ℤ_[p] D] (P : Ideal D) [P.IsPrime]`, exact sketch:
```lean
theorem quotient_free_of_prime_avoiding_p (hp : (p : D) ∉ P) :
    Module.Free ℤ_[p] (D ⧸ P)
```
Show the coefficient map injective using `PadicInt.ideal_eq_span_pow_p`, then
finite torsion-free over the PID implies free. Source: II Corollary 4.7's proof.
Reuse the argument in `B5Inputs.lean:76–90`; its `exists_domain_quotient` at 52
assumes D already free, so cannot supply this weaker-input lemma. Locality and
residue compatibility are follow-ups, not hidden conclusions of GL4.

After GL1–GL4, dispatch through the existing LF0 D1/D2/P1/K1 queues only
when the dictionary gates above have source-matched contracts. Their arithmetic
nonvanishing must supply GL3's premise; these four ready algebra leaves do not.
Final assembly will prove `freyLifting : FreyLifting` from the constructed ring,
HR specialization and residual witness, then rewire B4 and audit FLT. It must
not use `lifts`, `mem_isCompatible`, or unconditional FLT to construct that ring.

Read-only API evidence (rerun from baseline; `M=.lake/packages/mathlib/Mathlib`):
`rg -n 'toZMod_spec|ker_toZMod|toZMod_eq_residueField_comp_residue' "$M/NumberTheory/Padics/RingHoms.lean"`;
`rg -n 'maximalIdeal_eq_span_p|ideal_eq_span_pow_p' "$M/NumberTheory/Padics/PadicIntegers.lean"`;
`rg -n 'nilpotent_iff_mem_prime' "$M/RingTheory/Nilpotent/Lemmas.lean"`;
`rg -n 'complexConjugation_fixed_finrank|isAbsolutelyIrreducible|exists_domain_quotient' FLT/GaloisRepresentation/HardlyRamified`.
Acceptance per new module: foreground `lake build MODULE`, then
`lake exe runLinter MODULE` **one module at a time**, and scratch `#print axioms`
of its endpoints showing only standard axioms. Never lint the whole library.

Ready-contract check, 2026-09-30 18:34:57 UTC: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsReadySketches.lean`
exited 0 (`Scratch/lifts-ready-sketches.log`): GL1–GL3 proofs and GL4's type elaborate;
`#print axioms GaloisRepresentation.IsHardlyRamified.isAbsolutelyIrreducible` has only the three standard axioms.
