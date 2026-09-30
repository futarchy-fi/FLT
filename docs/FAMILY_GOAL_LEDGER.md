# GOAL-F0 — compatible-family source and hypothesis ledger

Checked 2026-09-30 UTC against `c557fcd66261f7de888076c086a7eb28df6539af`.
`gh api repos/futarchy-fi/FLT/commits/main --jq .sha` returned that commit;
`HEAD = origin/main`; the local `main` branch is stale (`71f9c3ac`).
Scope: deltas to [LF0](LIFT_FAMILY_PLAN.md), especially C1 and L2/L3;
[three-adic audit](THREE_ADIC_AUDIT.md) supplies the local source ledger.
This document neither proves existence nor replaces those plans' shared work estimates.

## Current admission and consumer

`FLT/GaloisRepresentation/HardlyRamified/Family.lean:29–68`, namespace
`GaloisRepresentation.IsHardlyRamified`, has exactly this type (comments omitted):
```lean
universe u v
open GaloisRepresentation IsDedekindDomain
open scoped TensorProduct
variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
theorem mem_isCompatible (hρ : IsHardlyRamified hpodd hv ρ) :
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
    σ.isCompatible ∧
    (∀ {ℓ : ℕ} (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A) (_ : Module.Finite ℤ_[ℓ] A)
        (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ])) (_ : IsModuleTopology ℤ_[ℓ] A)
        (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
        (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2) (τ : GaloisRep ℚ A W)
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ) ∧
    (∃ (_ : Algebra R (AlgebraicClosure ℚ_[p])) (_ : ContinuousSMul R (AlgebraicClosure ℚ_[p]))
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
        Fin 2 → AlgebraicClosure ℚ_[p]),
      (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ) := sorry
```
Declaration line 37; admission line 68. Finite **free** coefficients already fix
CORE_PLAN's historical characteristic-p counterexample. No irreducibility or
residual provenance is required by this statement; the literature below does require it.
`FLT/Assembly/ExistingInputs.lean:36` supplies
`theorem hardlyRamifiedCompatibleFamilies : HardlyRamifiedCompatibleFamilies`;
`Inputs.lean:50` defines that proposition as this type restricted to `Type`.
`FermatsLastTheorem.lean:19–25` consumes that adapter through
`PNat.pow_add_pow_ne_pow_of_three_inputs` (`Assembly/ThreeInputFinal.lean:24`).
`Assembly/PrimeField.lean:48–86` uses lifting, a domain quotient, this family,
one 3-adic model and trace descent. The other arithmetic inputs remain
`HardlyRamified/Lift.lean:37` (`lifts`, admission :48) and `Assumptions/Mazur.lean:103`
(`Mazur_statement`); their construction belongs to the lifting/Mazur ledgers.

Audit command, run in the foreground from this main snapshot on 2026-09-30:
`LEAN_NUM_THREADS=2 lake build FermatsLastTheorem > Scratch/build.log 2>&1`, then
`LEAN_NUM_THREADS=2 lake env lean Scratch/FamilyGoalAudit.lean > Scratch/family-goal-audit.log 2>&1`.
Recreate the scratch file by copying `FLTTest/AssemblyAxioms.lean` and appending
`#print axioms PNat.pow_add_pow_ne_pow` and
`#print axioms FLT.Assembly.hardlyRamifiedCompatibleFamilies`.
The copied guard recursively checks types and bodies for precisely the three
arithmetic leaves above and rejects a reachable legacy `three_adic`.
Checked at **2026-09-30 18:37 UTC**: build and scratch audit both exited 0.
Goal axioms: `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`;
family adapter: `[propext, sorryAx, Classical.choice, Quot.sound]`.
Recursive guard passed: exactly the three arithmetic leaves; no legacy `three_adic`.

## Sufficient restriction and source deltas

Use LF0's `CofiniteFrobeniusTrace` / `FreyResidualTraceInput` verbatim (also specified
below). Only irreducible Frey residual inputs with **p ≥ 17** need construction.
This is the weakest trace consequence consumed by the proof, not a claim of a
unique logically weakest proposition. Keep Mazur exclusion as an independent premise.
For the family boundary alone, select **one** lift/domain quotient with its original
residual isomorphism and construct **one** integral HR 3-companion and a common trace
field E. LF0 C1's two embeddings/common coefficients suffice; neither all primes,
all embeddings, purity, nor an exact family identification is needed for trace transfer.
Joint existence for that selected lift is essential: do not choose an arbitrary lift
and assume a companion theorem applies to it. Residual conjugacy must survive quotienting.

Primary texts checked by downloading PDFs to Scratch and extracting with `pypdf`:
[S] Snowden, *On two dimensional weight two odd representations of totally real fields*,
[arXiv:0905.4266v1](https://arxiv.org/pdf/0905.4266v1), numbering below is that version.
[B] Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of weight*,
Ann. Math. 179 (2014), [arXiv:1010.2561v4](https://arxiv.org/pdf/1010.2561v4).
These resolve a useful source for the blueprint's unexpanded `blggt` citation;
they do **not** certify the unrestricted Lean signature.

| Mathematical step | Precise source and required hypothesis / remaining gate |
|---|---|
| Select a lift with prescribed determinant/local behavior | [S] Thm. 7.2.1; lifting lane owns local solvability and residual hypotheses (A1)/(A2), not this family leaf. |
| Potential modularity of that lift | [S] Thm. 5.1.2, Prop. 8.2.1 for prescribed splitting. Requires finite ramification, oddness, weight two, and (A1): absolute irreducibility on `G_F(ζ_p)`. (A2)'s p=5 exception disappears at p≥17. HR determinant gives oddness; HR finite-flatness → weight two and (A1) still need bridges. AbsoluteIrreducibility.lean:99 proves absolute irreducibility over ℚ, **not (A1)**. |
| Attach p/3 members over the auxiliary field, one coefficient field | [S] Prop. 9.2.1 proof, p. 27: Hilbert forms `f_i`, coefficient fields `K_i`, common Galois field K containing the required roots of unity. Existing Attachment.lean:209,249,291,335 are admitted interfaces, not proofs of this step. |
| Solvable/Brauer descent, actual rank two and original identification | [S] Prop. 9.2.1, pp. 27–28: Frobenius reciprocity/Mackey give self-pairing 1; dimension 2 removes the negative sign. The original member is equivalent, not merely trace-compatible. A virtual representation is insufficient. |
| General compatible-family alternative | [B] Thm. 5.5.1 and §5.5(4),(8): polarized regular odd representation, potential diagonalizability, cyclotomic-restriction irreducibility, and ℓ≥2(n+1). Its CM-field/polarization conventions need specialization; it is not an unconditional theorem for this HR input. |
| Common good-prime traces | [S] Prop. 9.2.1 final paragraph / Rem. 9.2.2. Locally use the coefficient of X of the common quadratic polynomial, not equality between representations over different fields. |
| One integral HR model at 3 | [S] Rem. 9.2.2 points to Taylor, *On the meromorphic continuation of degree two L-functions*, Doc. Math., Extra Volume (2006), Thm. 6.6 for strong compatibility. This alone is **not** the integral HR assertion. Raynaud, BSMF 102 (1974), Thm. 3.3.3 / Cor. 3.3.6 give finite-flat model comparisons over ℤ₃ (`e=1<2`); an exact source-to-Lean construction of the flat model and the unramified square-trivial quotient at 2 remains a gate. Good-prime traces cannot replace it. |
| Three-adic trace 1+q | Existing `threeAdicFrobeniusTrace_of_primePowerSorting` plus `primePowerSortedExtensionExists`; sources: Schoof 2005 Prop. 3.1 proof, Prop. 5.1, Cor. 4.2; Ribet 1976 Prop. 2.1; Fontaine 1985 Thm. B(i). See THREE_ADIC_AUDIT §§2–3 for the precise local adaptations. Do not reopen that implementation queue. |
| Transfer to p, reduce, contradict irreducibility | Elementary injectivity/trace identities in `TraceCompatiblePair.transport_one_add` and `B5Inputs`; A literature route is Serre, *Linear Representations of Finite Groups*, §12.1, Thm. 30 (Brauer–Nesbitt), with the common quadratic characteristic polynomial. The existing Frobenius-trace criterion instead uses an elementary rank-two argument and a power-Frobenius cover; reuse it. No new family-existence theorem is hidden here. |

The source gaps above block arithmetic existence dispatch, not the three ready leaves.

## Ordered implementation queue (new modules; hard caps include all source lines)

**F1 — READY now; cap 250.** `FLT/Deformations/RepresentationTheory/FamilyTracePair.lean`.
This dispatches LF0 L2, not a second competing implementation. Import existing
`TraceCompatiblePair` and `B5Inputs`. In namespace `GaloisRepresentation`, define
`frobTrace` for `[CommRing R] [TopologicalSpace R] [AddCommGroup V] [Module R V]`:
```lean
noncomputable def frobTrace (ρ : GaloisRep ℚ R V) (q : ℕ) : R :=
  if hq : q.Prime then (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).trace R V else 0
-- E : Type*, [Field E] [NumberField E]; ℓ p : ℕ
theorem traceCompatiblePair_of_isCompatible
    (σ : GaloisRepFamily ℚ E 2) (hσ : σ.isCompatible)
    (hℓ : Fact ℓ.Prime) (φ : E →+* AlgebraicClosure ℚ_[ℓ])
    (hp : Fact p.Prime) (ψ : E →+* AlgebraicClosure ℚ_[p]) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
      TraceCompatiblePair φ ψ
        (fun q ↦ ∃ hq : q.Prime, 5 ≤ q ∧ q ≠ ℓ ∧ q ≠ p ∧
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ S)
        (frobTrace (σ hℓ φ)) (frobTrace (σ hp ψ))
```
Extract `S,Pv`, choose `a q = -(Pv vq).coeff 1` at primes, zero otherwise.
Anchors: `GaloisRepFamily.lean:58`; `B5Inputs.lean:252,280,288`
(`trace_eq_neg_coeff`, `prime_not_mem`, `compatible_trace`); no existence premise discharged.

**F2 — READY now, independent of F1; cap 300.** `FLT/Assembly/FreyTraceInput.lean`.
Dispatch LF0 L3 with namespace `FLT.Assembly`, imports `FLT.Assembly.Proof` and
`Mathlib.Topology.Instances.ZMod`; open `GaloisRepresentation` and scoped `NumberField`.
```lean
def CofiniteFrobeniusTrace {R V : Type} [CommRing R] [TopologicalSpace R]
    [AddCommGroup V] [Module R V] (p : ℕ) (ρ : GaloisRep ℚ R V) : Prop :=
  ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    ∀ q (hq : q.Prime), 5 ≤ q → q ≠ p →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).trace R V = 1 + q
def FreyResidualTraceInput : Prop :=
  ∀ P : FreyPackage, 17 ≤ P.p →
    letI : Fact P.p.Prime := ⟨P.pp⟩
    let ρ := P.freyCurve.galoisRep P.p P.hppos
    ρ.IsIrreducible → CofiniteFrobeniusTrace P.p ρ
theorem B4_of_freyResidualTrace (htrace : FreyResidualTraceInput) : FLT.Bosses.B4
theorem flt_of_freyResidualTrace (hmazur : MazurTorsionExclusion)
    (htrace : FreyResidualTraceInput) : FermatLastTheorem
```
Use Frey rank/HR determinant (`HardlyRamified/Frey.lean:95`), the criterion
`HardlyRamified/Chebotarev/FrobeniusTraces.lean:262`, and
`Assembly/Proof.lean:37` (`B3_of_torsionExclusion`), `Proof.lean:81,84`.
Install the p-adic `ZMod` algebra/local-hom as in `Assembly/PrimeField.lean:28,45`.
Use `PNat.pow_add_pow_ne_pow_of_FermatLastTheorem` (`FLT/Basic/Lemmas.lean:72`)
to reach the requested positive-natural goal. Do not call unconditional reducibility
or modify the final theorem until the trace premise has an actual proof.

**F3 — READY now, independent of F1/F2; cap 180.**
`FLT/Deformations/RepresentationTheory/BrauerEffectivityCoefficients.lean`.
Import `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Tactic.Linarith`,
`Mathlib.Tactic.Omega`;
namespace `GaloisRepresentation`; source [S] Prop. 9.2.1 proof, p. 28.
```lean
theorem effective_of_square_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℤ) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hself : ∑ i, (n i)^2 = 1) (hdim : ∑ i, n i * (d i : ℤ) = 2) :
    ∃ i, d i = 2 ∧ n i = 1 ∧ ∀ j, j ≠ i → n j = 0
```
Find a nonzero coefficient; nonnegative squares force all others zero and it to ±1;
positive dimension excludes −1. Anchors: `Finset.sum_pos_iff_of_nonneg`,
`Finset.single_le_sum`, `Finset.sum_eq_single`. This only proves the final coefficient
calculation: arithmetic self-pairing independence and an actual representation category
remain C1 prerequisites, not assumptions that F3 has discharged.

Next arithmetic work remains LF0 A1/P1/K1/C1, gated by the source matches above;
do not label whole attachment, descent or integral-model programs ≤400-line leaves.
F1/F2/F3 can land separately; C1 consumes F1/F3, and final witness assembly consumes F2.
Acceptance per leaf: foreground `lake build MODULE`, then `lake exe runLinter MODULE`
(one module at a time), and `#print axioms` showing only standard axioms for its conditional
endpoints. No `sorry`, new axioms, or calls to the admitted family/lift may prove those leaves.

Recheck API/dispatch evidence at the pinned commit (searches run 2026-09-30):
```sh
rg -n 'trace_eq_neg_coeff|prime_not_mem|compatible_trace' FLT/GaloisRepresentation/HardlyRamified/B5Inputs.lean
rg -n 'B3_of_torsionExclusion|B[23]_implies_B[12]' FLT/Assembly/Proof.lean FLT/Proof.lean
rg -n 'sum_pos_iff_of_nonneg|single_le_sum' .lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean
rg --files FLT | rg 'FamilyTracePair|FreyTraceInput|BrauerEffectivityCoefficients'
```
Last search returned no files: the three queued modules are new at this snapshot.

Signature check (2026-09-30 18:19 UTC): `LEAN_NUM_THREADS=2 lake env lean Scratch/FamilyGoalSketches.lean`
exited 0 for F1–F3 with explicit binders and Scratch-only `sorry` bodies; this checks
types, not proofs. This documentation-only delivery adds no library module; no lint was run.
