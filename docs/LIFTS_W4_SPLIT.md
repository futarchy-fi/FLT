# Lifting wave 4: finite-flat input and the weight-two boundary

Checked 2026-09-30 UTC at `bc287105` by the searches below. This refines the
finite-flat/weight-two gate of `LIFTS_GOAL_LEDGER.md`; it does not certify
that the arithmetic dictionary is ready. Three algebraic leaves are READY.
The two arithmetic leaves have exact target sketches but are BLOCKED on
foundations absent from both FLT and Mathlib. Caps include all module lines.

## Sources and choice of boundary

Khare–Wintenberger, *Serre's modularity conjecture II*, author manuscript:
https://www.math.ucla.edu/~shekhar/papers/proofs.pdf.
Read `Scratch/kw-proofs.txt:1152–1218` (§3.2.2), especially 1190–1191:
in the ordinary case finite flatness can occur only at weight 2; the selected
lift is then crystalline of weight 2 on inertia. The low-weight crystalline
problem is defined separately in (ii). Proposition 3.6 at 1259–1285 concerns
the ordinary local deformation rings, not a general flat/weight equivalence.
The irreducible case is treated in §3.2.3. For residual weight use Serre,
*Sur les représentations modulaires de degré 2*, Duke 54 (1987), §2.
For the integral direction the required missing input is the integral
Fontaine–Laffaille/Barsotti–Tate comparison, not just Hodge–Tate weights.

Two possible interfaces: name finite flatness “weight two”, or implement
Serre's independent inertia/extension-class definition and prove the bridge.
Choose the latter; the former would conceal the arithmetic theorem. Likewise,
do not define “crystalline” by the desired family of finite-flat quotients.
No arithmetic conclusion may be supplied as a record field.

Existing `Flat.lean:31,43` already proves quotient closure and
`HasFlatProlongationAt.isFlatAt`. `ResidualPointModule.lean:118` extracts a
bundled local model over a finite field for K=ℚ. Reuse the quotient theorem;
W4.1 supplies its general converse without importing the three-adic package.
Existing `B5Inputs.flatAt_quotient` handles continuous coefficient surjections;
W4.2 instead compares two reductions of the *same* representation directly.

## Shared Lean context for the ready leaves

Files live in `FLT/Deformations/RepresentationTheory/`, namespace `GaloisRep`.
Use `open NumberField` and `open scoped TensorProduct`.

```lean
variable {K M : Type u} {A : Type} [Field K] [NumberField K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : GaloisRep K A M)
```

### W4.1 — `FlatDiscrete.lean`, cap 180, READY

Import `FLT.Deformations.RepresentationTheory.Flat`. Exact target:

```lean
theorem isFlatAt_iff_hasFlatProlongationAt [IsLocalRing A] [DiscreteTopology A] :
    ρ.IsFlatAt v ↔ ρ.HasFlatProlongationAt v
```

Specialize `IsFlatAt.cond` to the open zero ideal; transport its Hopf witness
through `(A/0) ⊗ M ≃ M`. Prove equivariance on pure tensors. Converse is the
existing quotient-closure theorem. Dependencies: none of W4. Source role:
extract the actual residual finite-flat input used in II §3.2.2; no weight
conclusion yet. This applies to the discrete prime field of the FLT goal.

### W4.2 — `FlatReduction.lean`, cap 220, READY

Import `Flat` and tensor right exactness. Exact target in the shared context:

```lean
theorem hasFlatProlongationAt_quotient_of_le {I J : Ideal A} (hIJ : I ≤ J)
    (hI : (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v) :
    (ρ.baseChange (A ⧸ J)).HasFlatProlongationAt v
```

Tensor `Ideal.Quotient.factorₐ A hIJ` with the identity of M. Its underlying
additive map is Galois equivariant and surjective. Apply
`GaloisModule.IsFiniteFlat.quotient`; neither ideal needs to be open.
Dependencies: existing finite-flat quotient theorem only. Source role:
schematic quotient closure needed to pass from integral torsion models to
arbitrary open coefficient quotients; compare the integral requirement in
the ledger's II §3.2.2 row. Do not assume flatness of the target reduction.

### W4.3 — `FlatCofinal.lean`, cap 180, READY after W4.2

Import `FlatReduction`. Exact target (ι can be any Type*):

```lean
theorem isFlatAt_iff_of_cofinal [IsLocalRing A] {ι : Type*} (J : ι → Ideal A)
    (hopen : ∀ i, IsOpen (J i : Set A))
    (hcofinal : ∀ I : Ideal A, IsOpen (I : Set A) → ∃ i, J i ≤ I) :
    ρ.IsFlatAt v ↔ ∀ i, (ρ.baseChange (A ⧸ J i)).HasFlatProlongationAt v
```

Also specialize to `J n = Ideal.span {(p : A)^n}`, retaining the explicit
openness/cofinality hypotheses. These are topology obligations, not hidden
arithmetic flatness assumptions. The reverse implication chooses a smaller
basis ideal and applies W4.2. Source role: preserve **every** open quotient
when assembling an integral lift from torsion models. No assumption that
one residual model alone implies integral flatness. Automatic verification
of p-power cofinality for finite p-adic orders is a future topology leaf.

### W4.4 — `ResidualSerreWeightTwo.lean`, cap 400, BLOCKED

Proposed location: `FLT/GaloisRepresentation/HardlyRamified/`.
Exact intended specialization (using the existing HR context from the ledger,
with k=ZMod p and V : Type) is:

```lean
theorem residual_serreWeight_eq_two (hp17 : 17 ≤ p)
    (hρ : IsHardlyRamified hpodd hV ρ) : serreWeight p ρ = 2
```

`serreWeight` is a **proposed, absent** independently defined Serre weight,
not an executable current API. Definition must include inertia characters,
the reducible extension-class distinction, and normalization used by I Lemma
6.2; determinant cyclotomic comes from hρ.det. Dependencies: W4.1, that
definition, and Serre §2's finite-flat classification (ordinary and irreducible
cases). Once classification exists, this ≤400-line adapter extracts hρ.isFlat
and applies it. Do not dispatch its proof before those foundations; fitting
the classification itself into 400 lines is not claimed. No weight record.
Consumer: cyclotomic-restriction irreducibility, I Lemma 6.2(ii).

### W4.5 — `CrystallineIntegralFlat.lean`, cap 400, BLOCKED

Same proposed directory. For p≥17, O the integers of a finite extension E/ℚp,
W finite free over O, σ : GaloisRep ℚ O W, and v the p-adic place, target:

```lean
theorem isFlatAt_of_crystallineWeightTwo
    (hσ : IsCrystallineWeightTwo ((σ.baseChange E).toLocal v)) : σ.IsFlatAt v
```

`IsCrystallineWeightTwo` is **proposed, absent**, to mean crystalline with
Hodge–Tate weights {0,1} using an independent period-module definition.
Dependencies: period rings/representations, integral Barsotti–Tate comparison
for arbitrary stable lattices, and W4.3. The comparison must produce actual
finite-flat models of O/p^n ⊗ W; O has finite p-adic module topology, giving
cofinality. This leaf only assembles that comparison, within 400 lines;
constructing p-adic Hodge theory is an earlier unbounded foundation project,
not a dispatchable claim here. Source: II §3.2.2(ii)(a)'s Fontaine–Laffaille
condition at k=2. Extension from O to the original finite local coefficient
order remains a separate descent obligation: do not identify the two rings.

## Rerunnable API evidence and acceptance

```sh
M=.lake/packages/mathlib/Mathlib
rg -n 'HasFlatProlongationAt|class GaloisRep.IsFlatAt' FLT/Deformations/RepresentationTheory/GaloisRep.lean
rg -n 'theorem HasFlatProlongationAt' FLT/Deformations/RepresentationTheory/Flat.lean
rg -n 'residualPointModule_localModel' FLT/GaloisRepresentation/HardlyRamified/ResidualPointModule.lean
rg -n 'lemma IsFiniteFlat.(map|quotient)' FLT/GroupScheme/FiniteFlat.lean
rg -n 'factorₐ|factor_surjective' "$M/RingTheory/Ideal/Quotient/Operations.lean" "$M/RingTheory/Ideal/Quotient/Defs.lean"
rg -n 'theorem TensorProduct.map_surjective' "$M/LinearAlgebra/TensorProduct/RightExactness.lean"
rg -n 'SerreWeight|serreWeight|IsCrystalline|Barsotti' FLT "$M"
```

Checked anchors: GaloisRep:391,396; Flat:31,43; ResidualPointModule:118;
FiniteFlat:1144,2382; Operations:426; RightExactness:182. Last search finds
only prose mentions of Barsotti–Tate; there is no weight/crystalline API.
For W4.1–3 in order: foreground `LEAN_NUM_THREADS=2 lake build MODULE`,
then `LEAN_NUM_THREADS=2 lake exe runLinter MODULE` individually, and
scratch `#print axioms` for every new endpoint (standard axioms only).
Add each to FLT.lean, check `grep '^public import' FLT.lean | LC_ALL=C sort -c`,
then commit locally. Never push, lint the whole library, or claim `lifts` proved.
