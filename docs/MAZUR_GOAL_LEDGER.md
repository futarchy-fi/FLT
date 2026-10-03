# Mazur input to positive-natural FLT

## W14 frontier (supersedes the historical dispatch below)

Checked 2026-10-03 at local base `8425864c`; source checks and the complete new
split are in [MAZUR_G1_GROUP_SPLIT](MAZUR_G1_GROUP_SPLIT.md). This is a local
branch audit, not a fresh audit of GitHub main or the final compiled theorem.

- M1-G, M1-H, M2-N, R1–R3, P1–P5 and group G1–G4 are implemented.
- G5/E1–E5 is complete: `PolygonCoconeComparison`,
  `PolygonAtlasSmoothLocus`, `PolygonSmoothLocus` give the specified polygon
  comparison, exact smooth locus and its commutative group. The geometry
  split lists the node/one-gon atlas and descent prerequisites.
- W14 completed U1 scaling naturality (105/160, `3b763ba8`), U2 node scaling
  (139/240, `005eeca7`), H1 incidence kernel/cokernel (75/160, `d8a4622f`).
  Checked 2026-10-03 01:40 UTC: each module build/lint passed; all 64 new
  declarations passed the axiom audit reproduced in the group split.
  The phase split was committed first as `dc83a262`. All caps include helpers.
- U3–U12 whole-polygon action and its base-change laws, H2–H15 normalization
  sheaves/cohomology/properness/dimension/genus are blocked as detailed there.
  The proposed cap is 240 per module; unresolved helper proofs must be split
  before dispatch. Constant-unit actions do not establish the relative action.
- Full G1 moduli, G2 Eisenstein arithmetic and A1–A5 remain large source-design
  gates. Older 400/500-line budgets below are historical, not current releases.
- `rg -n "^axiom Mazur_statement" FLT/Assumptions/Mazur.lean` still returns
  line 103. `ExistingInputs` still uses `mazur_W`, and the final theorem still
  passes that input. No claim of removing the dependency is made.

The final path is: prove `NoLargePrimeTorsion`, rewire the existing adapter,
then rebuild and axiom-audit `PNat.pow_add_pow_ne_pow`. Editing that existing
Lean consumer is outside W14 authorization. Other final admissions are separate.

## Historical M0 audit and source ledger

Checked 2026-09-30 18:05 UTC against GitHub main `c557fcd66261f7de888076c086a7eb28df6539af`
(`gh api repos/futarchy-fi/FLT/commits/main --jq .sha`), equal to this task's base.
The local `main` ref was older; it was not used as the source snapshot.
This is a delta to [MAZUR_PLAN](MAZUR_PLAN.md), [MAZUR_CONTRACTS](MAZUR_CONTRACTS.md)
and [FCURVE_CONTRACTS](FCURVE_CONTRACTS.md), implementing audit split M0.
The queue below replaces their stale first-dispatch/status lists, not their arithmetic route.

## Current admission and consumers

Exact declaration, `FLT/Assumptions/Mazur.lean:103` (affine notation scope open):

```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) ∧
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

This is finiteness plus a cardinal bound, not the full classification statement.
`FLT/MazurW.lean:23` proves the following by consuming that axiom at line 31:

```lean
theorem mazur_W (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point,
      Function.Injective f
```

The actual final adapter is `FLT.Assembly.mazurTorsionExclusion`,
`FLT/Assembly/ExistingInputs.lean:24–28`. `FermatsLastTheorem.lean:19–25`
passes it to `PNat.pow_add_pow_ne_pow_of_three_inputs`
(`FLT/Assembly/ThreeInputFinal.lean:24`), with lifting and family inputs.
The conditional Frey consumer is `FreyPackage.mazur_of_torsionExclusion`
(`FLT/Assembly/Mazur.lean:41`); `FreyPackage.mazur` is an older direct caller.
These are proved adapters, not additional Mazur admissions.

Reproduction: copy `FermatsLastTheorem.lean` verbatim into
`Scratch/MazurGoalAudit.lean`, append `#print axioms` for the names below, then run
`LEAN_NUM_THREADS=2 lake env lean Scratch/MazurGoalAudit.lean` in the foreground.
Run `git diff --exit-code origin/main -- FLT FermatsLastTheorem.lean` to check
source equality. Checked 2026-09-30; scratch files/logs are deliberately uncommitted.
With S = `{propext, Classical.choice, Quot.sound}`, the observed sets are:

| Declaration | Axioms |
| --- | --- |
| `Mazur_statement`, `mazur_W`, `FLT.Assembly.mazurTorsionExclusion` | S + `Mazur_statement` |
| `FLT.Assembly.mazurTorsionExclusion_of_noLargePrimeTorsion` | S |
| `FreyPackage.mazur_of_torsionExclusion` | S |
| `PNat.pow_add_pow_ne_pow_of_three_inputs` | S |
| `PNat.pow_add_pow_ne_pow` | S + `Mazur_statement` + `sorryAx` |

The last set aggregates admissions; it does not say that Mazur contains a `sorry`.
Replacing this input leaves the lifting/family admissions to their own queues.

## Restricted target and source ledger

The weakest input at the Frey irreducibility call, allowing an assembly rewire, is
this proposition (no claim of a logically weakest axiom among all possible proofs):

```lean
∀ P : FreyPackage, 17 ≤ P.p →
  letI : Fact P.p.Prime := ⟨P.pp⟩
  GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos)
```

For the selected torsion route, retain the exact sufficient goal-specific restriction
`FLT/MazurWOfPrimeTorsion.lean:23`; it is a definition, currently without a proof:

```lean
def NoLargePrimeTorsion : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → 17 ≤ ℓ →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ¬ ∃ P : (E⁄ℚ).Point, addOrderOf P = ℓ
```

It is stronger than `MazurTorsionExclusion` (`FLT/Assembly/Mazur.lean:24`),
which excludes only an injected `(Z/2)² × Z/ℓ`; it is not the weakest Frey input.
The existing adapter at `FLT/Assembly/Mazur.lean:32` supplies that exclusion.
Do not restrict E to the original Frey curve: the quotient branch at
`FLT/FreyCurve/Mazur.lean:72` produces another E with full two-torsion.
Its current signature does not export geometric degree-p isogeny provenance.

[M] Mazur, *Modular curves and the Eisenstein ideal*, IHÉS 47 (1977), 33–186,
[primary PDF](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf).
Printed pages below; III §3–5 and I (2.9) rechecked by PDF text extraction today.
[DR] Deligne–Rapoport, LNM 349 (1973), 143–316; exact numbered statements and
scan links are in [DR_SOURCE_LEDGER](DR_SOURCE_LEDGER.md).
Serre (1987) means *Sur les représentations modulaires de degré 2 de
Gal(Q̄/Q)*, Duke Math. J. 54, 179–230, §4.1 Proposition 6.

| Mathematical step | Source and retained hypotheses |
| --- | --- |
| Torsion bound currently assumed | [M] III Theorem (5.1), p.156; each listed group has order ≤16. |
| Selected exclusion | [M] III Corollary (5.2), p.156, restricted to prime ℓ≥17. |
| Prime-level moduli, integral cusps | [M] II §1, pp.62–64; III §5 Step 3, p.159. |
| Generalized curves underlying that moduli | [DR] II Definitions 1.4, 1.12; retain smooth-or-polygon fibers and group action. |
| Eisenstein quotient | [M] II §9 definition; II (10.3)–(10.4), pp.97–98; quotient by completion-kernel images, not I·J. |
| Finite rational quotient and distinct cusps | [M] III (3.1), Lemmas (3.2)–(3.4), Corollary (3.5), pp.148–150. |
| Finite curve points | [M] III Theorem (4.1), pp.151–152; genuine nonconstant scheme map with finite fibers. |
| Semistability, components at 2,3 | [M] III §5 Steps 1–2, pp.158–159; p≥17, including local finite-flat rigidity at p. |
| Components at all bad primes | [M] III §5 Step 3, pp.159–160; T=Spec Z[1/(2p)], odd specialization including q-primary torsion. |
| Cyclotomic torsion extension | [M] III (5.4), p.157, third reduction and Step 4, pp.158,160; inverse cyclotomic conjugation and unramifiedness. |
| Triviality of that extension | [M] I Corollary (2.9), p.53; III third reduction, p.158; weight two, B₂=1/6. |
| Isogeny iteration contradiction | [M] III second reduction, pp.157–158, using (4.1); retain rational generator, no backtracking, cyclic composites. |
| Frey irreducibility consequence | Serre (1987), §4.1 Proposition 6; source pointer in MAZUR_CONTRACTS, not independently reread here. |

The coarse-point finite-fiber/twist obligation and geometric isogeny exports in A5
of MAZUR_PLAN remain required. The source's compressed second reduction is not an
already formalized proof of those steps. Small-prime classification is outside this goal.

## Merged deltas and bounded dispatch

FC08 now supplies `finiteDimensional_H1_of_proper`
(`FLT/Mazur/ProperCoherentCohomology.lean:41`) and actual `curveGenus`
(`ProperCurveGenus.lean:30`). `NodalGeometricFiberGenus.lean:76,83` adds genus-one
fiber predicates, canonical pullback and forgetting genus, in universe zero.
It does not prove constant sections/genus one for an arbitrary curve or a polygon.
`DRFiberClassification.lean:38` retains the independently supplied smooth-or-polygon
condition. Combining these conditions still does not construct DR's group/action.
G2-D1–D4/FC12–FC16 consumers are also present: `GenericFibers.lean:133,157,163,171`
contains nonconstancy, finite fibers and `g2CurveFinite`; do not schedule them again.
The genuine scalar cohomology field-extension comparison (FC09) remains separate.

All paths in the queue start with `FLT/Mazur/`; caps include headers and helpers.
The first two leaves are independent and ready now. They add no arithmetic hypotheses
that can be passed off as constructions. No Lean library changes belong to M0.

1. **M1-G: `NodalGenusOneBaseChange.lean`, cap 120, READY.**
   Import `NodalGeometricFiberGenus`; use its namespace
   `FLT.Mazur.FCurve.CurveFiberHypotheses`, open category/limits/scheme notation.

   ```lean
   theorem NodalGenusOneGeometricFibers.baseChange
       {X S T : Scheme} {f : X ⟶ S} [IsProper f]
       (h : NodalGenusOneGeometricFibers f) (g : T ⟶ S) :
       NodalGenusOneGeometricFibers (pullback.snd f g)
   ```

   Proof contract: apply `h.fiber` to each geometric square pasted horizontally
   with the base-change square. The resulting fiber structure map is unchanged;
   properness proofs agree by proof irrelevance. No tensor/cohomology comparison
   is assumed. Source: [DR] II Definition 1.4 (fiber condition) and pullback pasting;
   this only transports the existing necessary predicate, not full DR stability.
   API evidence: `rg -n 'paste_horiz|baseChange' FLT/Mazur/DRFiberClassification.lean`
   gives lines 61–66; `rg -n 'fiber :|pullback' FLT/Mazur/NodalGeometricFiberGenus.lean`
   gives lines 84–94. Dependencies are merged FC08 only.

2. **M2-N: `CuspOrderNumerator.lean`, cap 100, READY.**
   Namespace `FLT.Mazur`; import rational order/cast lemmas and required tactics.

   ```lean
   theorem cuspOrderNumerator_ge_two (p : ℕ) (hp : 17 ≤ p) :
       2 ≤ ((((p - 1 : ℕ) : ℚ) / 12).num.natAbs)
   ```

   Source: numerical part of [M] III (3.1) and §5 Step 3, p.160;
   n=numerator((p−1)/12). No primality is necessary for this inequality.
   Show the rational exceeds 1, then use positive integral denominator and
   `Rat.num_div_den` to force numerator ≥2. This proves no cusp-order theorem.
   API evidence: `rg -n 'num_div_den|den_pos' .lake/packages/mathlib/Mathlib/Data/Rat`
   finds `Lemmas.lean:164,321`, `Defs.lean:67`; declarations also come from Lean core.
   The search `rg -n 'cuspOrderNumerator' FLT` returns no existing declaration.
   A scratch proof passed `LEAN_NUM_THREADS=2 lake env lean Scratch/MazurNumeratorSketch.lean`
   on 2026-09-30 with axioms S only; the proposed library module remains unimplemented.

3. **M1-H: `ClassifiedGenusOneFamily.lean`, cap 200, AFTER M1-G.**
   Import M1-G and `DRFiberClassification`; use the FCurve namespace and open
   `CurveFiberHypotheses DRFiberClassification`. Freeze the record as follows:

   ```lean
   structure ClassifiedGenusOneFamily (f : X ⟶ S) : Prop where
     family : ProperFlatFamily f
     classified : ClassifiedGeometricFibers f
     genus : letI : IsProper f := family.1; NodalGenusOneGeometricFibers f
   theorem ClassifiedGenusOneFamily.baseChange {f : X ⟶ S}
       (h : ClassifiedGenusOneFamily f) (g : T ⟶ S) :
       ClassifiedGenusOneFamily (pullback.snd f g)
   ```

   Here `{X S T : Scheme}` are implicit variables. Also expose forgetful maps to
   `ClassifiedFamilyCore` and `NodalFamilyCore`, preserving every input condition.
   Sources: [DR] I.1.0, II.1.4; actual genus uses Stacks 0BY7 and finiteness 02O6.
   API: `rg -n 'properFlatBaseChange' FLT/Mazur/FamilyTransport.lean` (line 72);
   `rg -n 'baseChange|toNodalFamilyCore' FLT/Mazur/DRFiberClassification.lean`.
   This is family-contract integration only; polygon genus and group actions remain open.

After these leaves, retain the construction gates in MAZUR_CONTRACTS G1/G2 and
MAZUR_PLAN A1–A5; they need new source-lemma subdivisions before dispatch, each ≤400
lines. In particular, moduli, Picard/Jacobian, Néron and arithmetic finiteness are
not single bounded leaves. The later `PrimeTorsionConclusion.lean` (cap 150) must
prove `theorem noLargePrimeTorsion : NoLargePrimeTorsion` from those constructions.
Only then rewire ExistingInputs with the existing adapter (cap 80) and rerun the
final axiom check. No completed FC08 theorem alone discharges the Mazur admission.
