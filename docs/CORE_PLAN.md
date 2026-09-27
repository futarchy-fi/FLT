# Core plan for the remaining FLT admissions

## Integration checkpoint — 2026-09-27

Checked at **2026-09-27 22:42 UTC** against
main `88768218` plus the changes in this commit.

The source audit below is historical. In particular, the coefficient-ring defect
described there has been repaired: `Family.lean` now requires
`Module.Free ℤ_[p] R`. Its proof is still admitted.

PRs #155–#159 are integrated in main; the consolidation builds their endpoints together.
Fresh `#print axioms` checks found only `propext`, `Classical.choice`, and
`Quot.sound` for:

- `ThreeAdicPlan.raynaud_extend_generic_morphism_unique`;
- `ThreeAdicPlan.FiniteContinuousGaloisModule.integralEtaleModel`;
- `ThreeAdicPlan.no_quadratic_extension_auxiliary`;
- `ThreeAdicPlan.character_eq_one_or_of_each_power_quotient`;
- `StableLattice.isExtensionOf_of_trivial_quotient`.

These checks are executable in `FLTTest/ThreeAdicConsolidation.lean`.
The character lemma allows a separate choice at each ideal-power level;
compatibility forces one global character. It does not supply the arithmetic
classification of those levels. The Ribet adapter identifies the residual
subcharacter from the determinant and a given invariant surjective functional.
It does not construct that functional (the admitted `mod_three` input).

Remaining three-adic work must distinguish these interfaces:

1. Raynaud **existence**, and patching the étale model with the model at 3.
   Uniqueness of an extension does not construct it.
2. The augmented-field discriminant bound and its hypotheses.
   The specialized quadratic exclusion is proved; it does not supply this bound.
3. Simple-object classification, reverse-extension vanishing, and sorted
   filtrations, yielding the invariant residual quotient and pure finite levels.
4. Assemble the domain-coefficient trace theorem with the existing normalization,
   lattice-transfer, Ribet, and character infrastructure.

`lifts`, `mem_isCompatible`, `three_adic`, and `Mazur_statement` remain the
four core obligations. No admitted endpoint was replaced in this consolidation.
Shrinking lifting, companion, or Mazur interfaces is useful only alongside a
proof; merely changing the location or name of an admission is not progress.

## Original source audit


Checked at **2026-09-27 16:25 UTC**, by reading and searching this worktree.
FLT source: `e564b0801563049c905f1e7505f2809719101e6a`;
Mathlib: `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
Task: `pool-yyahe.40`. This is a scoping document, not a proof certificate.
No Lean execution or build was performed: the worktree has no project build.
The axiom list in the brief agrees with the checked-in `#guard_msgs` in
`FermatsLastTheorem.lean:31`; it was **not independently reprinted** here.

Recommend preserving the current B5 argument while shrinking its inputs:

* Prove a **domain-coefficient 3-adic trace theorem**, sufficient for the
  family member actually used, before tackling arbitrary nonreduced rings.
* Replace the all-primes compatible family by a **p/3 trace companion** for
  the particular irreducible residual lift. Include that residual hypothesis.
* Construct the lift only over `ZMod p`, `p ≥ 5` (or `p ≥ 17` after restricting
  B5 to its FLT consumer), with a domain coefficient ring from the start.
* Replace the full `Mazur_statement` by the exclusion `mazur_W` actually used,
  or by the prime-torsion theorem for primes **at least 17** that implies it.
  This eliminates the general torsion-cardinality axiom from the path if the
  replacement is proved; it does not make the arithmetic theorem elementary.

**Statement defect:** `mem_isCompatible` permits positive-characteristic
coefficient domains but concludes that they embed into characteristic zero.
The standard split representation gives a mathematical counterexample; see F.
Its actual caller has the missing finite-free coefficient hypothesis. Do not
try to prove the unrestricted statement unchanged.

There are useful S-sized algebra leaves below. None of the four arithmetic
endpoints is a capped-worker task. Lifting and companions share a large
potential-modularity/deformation-theory development. A new axiom asserting
one of the smaller interfaces is only a smaller admission, not completion.

## Use sites and the path to FLT

`F/` means `FLT/`; `M/` means `.lake/packages/mathlib/Mathlib/`.
The table contains **all direct executable uses** of the four names found in
project Lean source, excluding declarations, comments, and unrelated
`Polynomial.lifts`. Qualified and dot-notation searches are recorded below.

| Admission | Definition | Direct use | Actual demand |
|---|---|---|---|
| `GaloisRepresentation.IsHardlyRamified.lifts` | `F/GaloisRepresentation/HardlyRamified/Lift.lean:35` | `PrimeField.lean:53`, `hρ.lifts hpodd V hV ρ hirr` | Only `k = ZMod p`, `5 ≤ p`, rank two, and the irreducibility assumption introduced at line 49 |
| `GaloisRepresentation.IsHardlyRamified.mem_isCompatible` | `Family.lean:37` | `PrimeField.lean:61`, `hσA.mem_isCompatible hpodd hWA` | Only the domain quotient of that lift; only its p-adic member and **one** 3-adic member |
| `GaloisRepresentation.IsHardlyRamified.three_adic` | `Threeadic.lean:31` | `PrimeField.lean:72`, `hη.three_adic U hU q hq hq5` | Only the family's integral 3-adic model `B`, which already has `IsDomain B`; only its Frobenius traces outside a finite set |
| `Mazur_statement` | `F/Assumptions/Mazur.lean:103` | `F/MazurW.lean:31` inside `mazur_W` | Both finiteness and `ncard ≤ 16`, solely to contradict an injection of a group of order `4*p`, where `p ≥ 17` |

The first three feed exactly this spine:

```text
lifts → exists_domain_quotient / hardlyRamified_quotient
      → mem_isCompatible → its 3-adic model → three_adic
      → compatible_trace → trace descent to ZMod p
      → not_isIrreducible_of_frobenius_traces
      → IsHardlyRamified.not_isIrreducible_of_prime_field
      → FreyCurve.torsion_not_isIrreducible (HardlyRamified/Frey.lean:112)
      → FLT.Bosses.B4_proof (Proof.lean:104)
      → B3_proof → B2_proof → B1_proof → flt
      → PNat.pow_add_pow_ne_pow (FermatsLastTheorem.lean:23)
```

The other branch is:

```text
Mazur_statement → mazur_W
 → FreyPackage.mazur (FreyCurve/Mazur.lean:92)
 → FLT.Bosses.B4_implies_B3 (Proof.lean:98)
 → B3_proof → B2_proof → B1_proof → flt → PNat.pow_add_pow_ne_pow
```

`B2_implies_B1` handles exponents below 17 using `FLT_small` from FltRegular.
Thus the final proof needs **all primes ≥17**, not just a finite list of
primes 17, 19, ... . The generic B5 theorem currently handles primes ≥5.
Restricting its consumer to ≥17 is possible but does not dispatch the general
arithmetic by a finite computation.

`mazur_W_ge11` in `F/MazurW.lean:50` and `mod_three` in
`HardlyRamified/ModThree.lean:26` contain `sorry` but are **not used by the
current proof bodies above**. Importing a file is not a theorem dependency.
Using either tomorrow creates a new obligation; neither is a proved shortcut.
The old `docs/CHEBOTAREV_PLAN.md` predates the present Chebotarev implementation;
its style is reused here, not its old completion status.

## Exact present statements

These blocks preserve the source statements and their surrounding variables;
only proof bodies and explanatory comments are omitted. They are quotations,
not proposed changes. In the first block `Frob` has the source local notation
`Field.AbsoluteGaloisGroup.adicArithFrob`; all four are in the namespaces shown.

### `three_adic`

In namespace `GaloisRepresentation.IsHardlyRamified`:

```lean
theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (hp : Nat.Prime p) (hp5 : 5 ≤ p),
      letI v := hp.toHeightOneSpectrumRingOfIntegersRat -- p as a finite place of ℚ
      (ρ.toLocal v (Frob v)).trace _ _ = 1 + p
```

### `mem_isCompatible`

In namespace `GaloisRepresentation.IsHardlyRamified`; open
`GaloisRepresentation IsDedekindDomain` and scoped `TensorProduct`.

```lean
universe u v

variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
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
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ) ∧
    (∃ (_ : Algebra R (AlgebraicClosure ℚ_[p])) (_ : ContinuousSMul R (AlgebraicClosure ℚ_[p]))
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
        Fin 2 → AlgebraicClosure ℚ_[p]),
      (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ)
```

### `lifts`

In namespace `GaloisRepresentation.IsHardlyRamified`; open `TensorProduct`.

```lean
universe u v

variable {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2)

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
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ
```

### `Mazur_statement`

Open scoped `WeierstrassCurve.Affine`:

```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) ∧
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

## Inventory: usable code versus mathematical obligations

“Body present” below means inspected source, **not a fresh transitive axiom
check**. A future proof must run `#print axioms` on every reused endpoint.

| ID | Existing API / location | What it buys; limitation |
|---|---|---|
| E1 | `IsHardlyRamified`, `HardlyRamified/Defs.lean:96` | Cyclotomic determinant, unramified outside `2p`, flatness at p, and an unramified rank-one quotient at 2 whose character squares to 1 |
| E2 | `GaloisRep.IsFlatAt`, `F/Deformations/RepresentationTheory/GaloisRep.lean:396`; `HasFlatProlongationAt` at 391 | Flatness for **every open coefficient ideal**; not just a single residual finite-flat condition |
| E3 | `B5Inputs.exists_domain_quotient`, `.flatAt_quotient`, `.hardlyRamified_quotient`, `HardlyRamified/B5Inputs.lean:52,106,160` | Bodies present. Domain quotient and continuous quotient preservation are already implemented; do not redispatch them |
| E4 | `B5Inputs.trace_toLocal_baseChange_conj`, `.trace_toLocal_baseChange`, `.padic_domain_map_injective`, same file:226,240,261 | Bodies present. Existing descent from characteristic-zero traces to residual traces |
| E5 | `B5Inputs.compatible_trace`, same file:288 | Body present. Uses only `-(Pv v).coeff 1` and injectivity of a number-field embedding; neither a full semisimplification API nor all polynomial coefficients are needed |
| E6 | `B5Inputs.cyclotomicCharacter_adicArithFrob`, `HardlyRamified/Chebotarev/FrobeniusTraces.lean:145`; `.not_isIrreducible_of_frobenius_traces` at 262 | Bodies present. The weak-Chebotarev trace endgame is already connected; it is not a missing core leaf |
| E7 | `IsHardlyRamified.mod_three`, `HardlyRamified/ModThree.lean:26` | **Admitted.** Its conclusion is a surjective *trivial quotient*, stronger than reducibility or a trace formula |
| E8 | `Odlyzko.not_discriminant_le_fontaine_bound`, `F/Odlyzko.lean:42`; `Odlyzko.Odlyzko_statement` at 29 | Bodies present. Totally complex fields of degree ≥18 cannot satisfy the displayed Fontaine upper bound; the representation-to-field discriminant bound and small-degree analysis are not supplied |
| E9 | `GaloisModule.IsFiniteFlat.quotient`, `.prod`, `F/GroupScheme/FiniteFlat.lean:2382,1156`; `HopfAlgebra.IsFiniteFlat.quotient` at 171 | Bodies present. Subquotient/Hopf-order infrastructure, not Fontaine's ramification estimate or a classification of all such group schemes |
| E10 | `Deformation.isCorepresentable_deformationFunctor`, `F/Deformations/Representable.lean:38`; `MoritaReconstruction.exists_universalTraceLift`, `DeSmitLenstra/UniversalTraceLift.lean:43` | Bodies present. Unrestricted deformation representability, requiring absolute irreducibility. **Not** existence of a characteristic-zero point with the prescribed local conditions |
| E11 | `SLiftFunctor`, `narrowSLiftFunctor`, `isCorepresentable_narrowSLiftFunctor`, `Representable.lean:89,104,114` | Local-condition functors exist; the last theorem is **admitted**. Context is a totally real field of even degree and `3 < l`, not the full `lifts` signature |
| E12 | `ker_RtoT_le_nilradical`, `F/Patching/REqualsT.lean:86` | Body present. Conditional commutative-algebra endgame given an actual patching system, nonzero modules, finiteness, depth/dimension and compatibility data. Not an arithmetic R=T theorem ready to apply |
| E13 | `PoitouTateData`, `greenbergWilesOrderFormula`, `F/PoitouTate.lean:46,87` | **Statement-layer scaffold.** The order formula is a field of the supplied data; the theorem projects it. No actual Galois duality theorem is obtained by importing it |
| E14 | `ContRepresentation`, `ContinuousCohomology` in `F/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` | Continuous-cochain infrastructure exists. Arithmetic local duality, global exactness and local-condition computations still need construction |
| E15 | `GaloisRep.IsAttachedAtGoodPrimes`, `F/GaloisRepresentation/Attachment.lean:135` | A usable predicate. `exists_galoisRep_isAttachedAtGoodPrimes` (209), `exists_integralModel_of_isAttachedAtGoodPrimes` (249), `exists_tameRankOneQuotient_of_isAttachedAtGoodPrimes` (291), `exists_flatIntegralModel_of_isAttachedAtGoodPrimes` (335) are **all admitted** |
| E16 | `cyclic_base_change`, `quadratic_cm_automorphic_induction`, `F/GaloisRepresentation/Automorphic.lean:139,237` | **Admitted.** Potential automorphy and descent cannot be waved away as existing imports |
| E17 | `Slop.OddRep.isIrreducible_baseChange_of_finrank_eigenspace_eq_one`, `F/Slop/RepresentationTheory/OddAbsIrredSlop.lean:446` | Body present. Irreducibility implies absolute irreducibility if one group element has a one-dimensional fixed space. Still need the complex-conjugation/cyclotomic bridge |
| E18 | `FreyPackage.mazurW_counterexample_of_reducible`, `F/FreyCurve/Mazur.lean:35`; `fullTwoTorsion_survives_of_kernel_killed`, `F/MazurW.lean:61` | Bodies present. The counterexample curve can be the Frey curve **or an odd-isogenous quotient**; surviving full two-torsion is already handled |
| E19 | `GaloisRep.trivial_of_everywhere_unramified`, `F/FreyCurve/Serre/UnramifiedCharacter.lean:95`; `intermediateField_eq_bot_of_localInertia` at 54 | Bodies present. The former is specialized to `ZMod p`; the latter supports general finite-image/Minkowski arguments. A p-adic character version needs finite-quotient passage |
| E20 | `FiniteFlatCommGroupScheme`, `F/MazurChapter/AdmissibleGroupSchemes.lean:37` | A framework with **admitted** constant/multiplicative objects, order-prime classification, fppf sheaf/cohomology constructions and cohomology bounds. It is not a completed Mazur chapter |
| E21 | `Matrix.trace_fin_two`, `Matrix.trace_fin_two_of`, `M/LinearAlgebra/Matrix/Trace.lean:220,232`; `LinearMap.det_eq_zero_iff_ker_ne_bot`, `M/LinearAlgebra/Determinant.lean:357` | Rank-two linear algebra for bounded wrapper leaves |
| E22 | `IsHausdorff.eq_iff_smodEq`, `IsHausdorff.haus`, `M/RingTheory/AdicCompletion/Basic.lean:68,60` | Separatedness turns equality modulo all ideal powers into equality; it does not produce the congruences |
| E23 | `AddCommGroup.torsion`, `M/GroupTheory/Torsion.lean`; `addOrderOf_dvd_iff_nsmul_eq_zero`, finite cyclic group/cardinality APIs | Abstract torsion arithmetic. Does not bound rational elliptic-curve torsion |
| E24 | `M/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, `.../DivisionPolynomial/`, `M/NumberTheory/ModularForms/`, `M/RingTheory/WittVector/` | Curve points, division polynomials, analytic modular forms and Witt vectors exist. No Mazur torsion theorem or integral modular-curve/Eisenstein-quotient package was located |

Searches for Fontaine, Ribet stable lattices, Mazur torsion, crystalline
representations and Eisenstein ideals did not find the required mathematical
endpoints in pinned Mathlib. Its `EllipticCurve/Jacobian/` files concern
**Jacobian coordinates**, not Jacobian varieties of modular curves. Its
level-one modular-form dimension formulas do not compute weight-two level-two
forms automatically. The repo has quaternionic automorphic forms and Hecke
operators; these are substantial foundations, not the missing attachment and
potential-modularity proofs.

## Statement conventions and estimates

New identifiers below are **proposed**. Code blocks are Lean-shaped statement
sketches, not elaboration-tested code. In a leaf, inherit the relevant exact
statement's coefficient/module/topology instances above unless explicitly
restricted. `HR ρ` abbreviates `IsHardlyRamified hpodd hV ρ`, with its prime,
rank equality and instances; it is not an extra arithmetic hypothesis.

For concise trace statements use this new, purely notational abbreviation:

```lean
noncomputable abbrev frobTrace (ρ : GaloisRep ℚ R V)
    (q : ℕ) (hq : q.Prime) : R :=
  (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
    (Field.AbsoluteGaloisGroup.adicArithFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)).trace R V
```

A finite set below is a `Finset` of `HeightOneSpectrum (𝓞 ℚ)`; `q ∉ S`
in prose means `hq.toHeightOneSpectrumRingOfIntegersRat ∉ S`. This avoids
silently changing the chosen Frobenius or the exceptional-prime convention.

S = roughly 20–100 new proof lines, 1–4 expert hours; M = 100–400 lines,
1–4 days; L = 400–1,500 lines, 1–4 weeks; XL = a development exceeding
1,500 lines, usually months. These are **planning estimates**, not measured
throughput. A cap means 2–4 hours. Only a leaf explicitly marked **now** is
suitable for immediate capped dispatch. An XL row is a named research boundary
with an output contract, not a claim that an opaque predicate hides small work.
It must be refined after the indicated mathematical/API question is settled.

## T: the 3-adic input

### Mathematical route and the scope reduction

The blueprint `ch03freyreduction.tex:216–277` specifies the route:
Fontaine's discriminant estimates plus Odlyzko/Poitou bounds establish the
mod-3 classification, then classify 3-adic representations. Its proofs are
marked TODO, so it is a **route reference, not a supplied detailed proof**.
Use Fontaine, *Il n'y a pas de variété abélienne sur Z*, Invent. Math. 81
(1985), 515–538, for the finite-flat ramification/discriminant method.
The precise variant allowing the prescribed ramification at **2** must be
proved; Fontaine's no-good-reduction-everywhere theorem alone does not imply
this result. E8 already gives the relevant numerical contradiction.

For domain coefficients normalize into the integers of a finite extension
of `ℚ_[3]`. Use finite-flat subquotients and lattice transport to keep HR under
changes of stable lattice. A Ribet stable-lattice argument rules out an
irreducible characteristic-zero representation whose residual constituents
are 1 and cyclotomic: an appropriate lattice gives the nonsplit extension
in the orientation forbidden by the **trivial-quotient** conclusion of
`mod_three`. A reference for that lattice method is Ribet, *A modular
construction of unramified p-extensions of Q(μ_p)*, Invent. Math. 34 (1976),
151–162. That paper does not itself supply the HR-at-2 preservation lemma.
Then classify the two rank-one characters using finite-flat local conditions
at 3 and triviality of globally unramified characters (Minkowski via E19).
Their sum is `1 + χ₃`; E6 evaluates χ₃ at Frobenius. Raynaud, *Schémas en
groupes de type (p,...,p)*, Bull. Soc. Math. France 102 (1974), 241–280, and
Tate's p-divisible-group theory are references for the local finite-flat work.

Do **not** claim reducibility of the residual representation implies
reducibility of the lift. Do **not** prove only mod-3 trace congruences and
conclude exact 3-adic traces. The oriented mod-3 statement, all stable lattices,
and the rank-one classification are real steps.

The existing `three_adic` allows nonreduced finite free local `ℤ_[3]`-algebras.
A field-valued proof does not see nilpotents. For FLT, restrict to `IsDomain R`
(the caller already has it), or even prove the trace after the specified
embedding into `AlgebraicClosure ℚ_[3]`. Equality outside a finite exceptional
set is enough after enlarging the compatibility exceptional set. This avoids
both all-ring and all-prime claims. It does not avoid the domain theorem.

### Leaves

**T0 — domain-only use-site adapter. S; now, conditional interface only.**
Input a theorem with the exact `three_adic` hypotheses plus `[IsDomain R]`.
Output the same `htrace3` used at `PrimeField.lean:67`.

```lean
theorem trace_of_domain_model
    [IsDomain B] (hη : IsHardlyRamified (by decide : Odd 3) hU η)
    (ht : ∀ q (hq : q.Prime), 5 ≤ q → frobTrace η q hq = 1 + q)
    (he : (η.baseChange (AlgebraicClosure ℚ_[3])).conj e3 = τ3) :
    ∀ q (hq : q.Prime), 5 ≤ q → frobTrace τ3 q hq = 1 + q
```

Reuse E4, map numerals, and the existing three-line calculation. Dependency:
E4 only; the arithmetic trace input remains explicit. Acceptance: no call to
`three_adic` in this adapter. It closes **no** arithmetic admission by itself.

**T1 — trace from a rank-one trivial quotient. S–M; cap only the matrix case now.**

```lean
theorem trace_eq_one_add_det_of_trivial_quotient
    [Field K] [FiniteDimensional K V] (hV : Module.finrank K V = 2)
    (A : Module.End K V) (π : V →ₗ[K] K) (hs : Function.Surjective π)
    (hπ : π.comp A = π) : A.trace K V = 1 + A.det
```

Choose a basis of `ker π` and a vector mapping to 1. The resulting triangular
matrix has one diagonal entry 1. E21 and Mathlib basis/kernel APIs suffice.
The **actually small** first leaf is the same theorem for `Matrix (Fin 2)
(Fin 2) K` with bottom row `(0,1)`, by `Matrix.trace_fin_two` and `det_fin_two`.
The general basis adaptation may exceed a cap; do not extend this to arbitrary
local rings without proving the kernel is free. Depends on no arithmetic.

**T2 — integral models and preservation under stable lattices. L; no.**
Normalize a finite domain coefficient order, extend the representation to its
fraction field, construct/transport a stable free rank-two lattice, and prove
HR for each lattice whose generic fibre is the given representation.

```lean
theorem hardlyRamified_of_stable_lattice
    (hρ : HR ρ) (L : StableLattice ρK) : HR L.representation
```

`StableLattice ρK` is proposed data: a Galois-stable full finitely generated
free submodule of the two-dimensional fraction-field representation, with its
inclusion and spanning proof. Output HR includes **all open-ideal** flatness
and the saturated rank-one quotient at 2, not just determinant/unramifiedness.
Dependencies: E2/E9, normalization and finite-extension DVR/module topology.
Mathlib's integral closure and DVR modules help; E3 alone is a quotient-of-
coefficients theorem, not a stable-lattice theorem. This also supplies scalar
extension to the normalization, which is not licensed by E3.

**T3a — Fontaine bound for the residual splitting field. XL; no.**

```lean
theorem residual_field_discriminant_bound (hρ : HR ρbar) :
    |(NumberField.discr L : ℝ)| ≤
      ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^
        Module.finrank ℚ L
```

Here `L` is the finite Galois extension cut out by the **specified residual
representation or auxiliary representation used in the classification**.
Before implementation, establish on paper which field has this bound, that
it is totally complex, and how its degree is related to the image. The
constant is the input of E8, not a claim that every finite quotient in an
arbitrary 3-power tower has the same bound. Dependencies: E9, ramification
filtrations/different, local calculation at 2, global discriminant product.
Mathlib has ramification/discriminant APIs, not this Fontaine theorem.

**T3b — classify the remaining residual images and extension orientation.
XL; no.** Acceptance is the **exact current `mod_three` statement** E7,
with a surjective invariant quotient, for every finite residue field of
characteristic 3. Combine T3a/E8 with the remaining small-degree fields,
finite-image group theory, and extension/local-condition analysis. A degree
bound or a semisimplification `1 ⊕ χ̄₃` is not enough. Dependencies: T3a,
E8, local finite-flat extension theory; finite group/Galois infrastructure
exists, this classification does not. For the full 3-adic statement's
normalization route the residue field need not be `ZMod 3`.

**T4a — Ribet lattice obstruction. L–XL; no.**

```lean
theorem not_irreducible_generic_of_all_lattices_trivial_quotient
    (hres : ResidualSemisimplification ρK 1 χbar3)
    (hL : ∀ L : StableLattice ρK,
      HasTrivialQuotient L.residualRepresentation) : ¬ ρK.IsIrreducible
```

The proposed predicates mean, respectively, residual composition factors
1 and χ̄₃, and the surjective equivariant quotient in E7. Require their
distinctness. Formalize the stable-lattice argument; use T2/T3b for its inputs.
No such theorem was located in Mathlib or this repo. Generic reducibility is
the output, not yet the desired trace identity.

**T4b — rank-one character classification. L–XL; no.**

```lean
theorem trace_generic_eq_one_add_cyclotomic
    (hρ : HR ρ) (hred : ¬ ρK.IsIrreducible) :
    ∀ g, (ρK g).trace K VK = 1 + algebraMap ℤ_[3] K (χ3 g)
```

`ρK` is the fraction-field base change, `VK` its module, and `χ3 g` the
exact cyclotomic character in E1. Prove local rank-one finite-flat characters
have the allowed weights, identify the two characters, and kill their
unramified twists using E19 generalized through finite quotients. At 2 the
unramified quotient and cyclotomic determinant are essential. Dependencies:
T2, finite-flat rank-one theory, E19; ordinary `GroupCohomology` is insufficient.
Then T1/E4/E6 descend/evaluate the trace, completing the domain theorem.

**T5 — equality from all power-quotient equalities. S; now, optional.**

```lean
theorem eq_of_all_power_quotients [CommRing R] (I : Ideal R)
    [IsHausdorff I R] {x y : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x =
      Ideal.Quotient.mk (I ^ n) y) : x = y
```

E22 plus the ideal-quotient equality criterion; likely a short wrapper.
Useful if an alternative Artin-quotient trace proof is chosen. It does not
supply any higher congruence and is not required by the domain/lattice route.

**T6 — arbitrary finite free coefficient rings. XL/unpriced; no; defer.**
The output is the exact present `three_adic` statement without `IsDomain`.
Need a rigidity theorem controlling traces in nilpotent directions, or
trace identities modulo **all** relevant ideal powers followed by T5. Taking
all maps into fields gives equality only modulo the nilradical. The domain
proof T2–T4 does not settle this. Do not budget this optional strengthening
as a routine generalization.

## F: compatible families, reduced to a p/3 companion

### Mathematical route and the hypothesis mismatch

`PrimeField.lean` uses the family only to obtain one integral 3-adic model
and transport rational traces back to the p-adic lift. It discards all other
members, the unramifiedness conjunct of compatibility at this stage, and all
coefficients except the trace coefficient. A common number field with two
embeddings and common traces outside a finite set suffices.

The standard route is potential modularity of the p-adic representation over
a suitable totally real extension; attach compatible systems to the resulting
Hilbert/quaternionic automorphic form; use solvable descent/Brauer induction
and irreducibility to descend the system to `ℚ`; prove local compatibility
strong enough to recover finite-flatness at 3 and the specified quotient at 2.
Weight/Hodge–Tate data alone does not give the last integral assertions.

References: Taylor, *On the meromorphic continuation of degree two L-functions*,
Doc. Math., Extra Volume: John H. Coates' Sixtieth Birthday (2006), 729–779;
Khare–Wintenberger, *Serre's modularity conjecture II*, Invent. Math. 178
(2009), 505–586 (the blueprint's `kwII`, DOI `10.1007/s00222-009-0206-6`);
Taylor, *On Galois representations associated to Hilbert modular forms*,
Invent. Math. 98 (1989), 265–280, for attachment. Precise hypotheses and local
variants must be matched before using a theorem from these papers. For
potentially semistable local compatibility, the existing Attachment file
explicitly separates integrality, tame quotient, and flatness obligations;
reuse that separation rather than calling all of it “compatibility”.

**Coefficient defect in the exact Lean statement:** `[IsDomain R]` and
`[Module.Finite ℤ_[p] R]` do **not** imply characteristic zero or a free
`ℤ_[p]`-module. For example take `p = 3`, `R = ZMod 3` with its usual
`ℤ_[3]`-algebra and discrete/module topology, and the split representation
`χ̄₃ ⊕ 1` on `R²`. Its determinant is cyclotomic; it is unramified outside 3;
at 3 it is the generic fibre of `μ₃ × (ℤ/3)`, hence finite flat; and at 2 it
has the required trivial unramified rank-one quotient. It is hardly ramified.
But the conclusion includes `Algebra (ZMod 3) (AlgebraicClosure ℚ_[3])`, which
is impossible: the image of `3 = 0` would say `3 = 0` in a characteristic-zero
field. Thus the current theorem is **mathematically false as stated**.
This is a paper counterexample checked against the definitions, not an
elaborated Lean counterexample in this no-build task. A useful future
regression witness would formalize the split finite-flat representation.

Repair by requiring finite freeness/torsion-freeness over `ℤ_[p]` (or an
injective structural map/characteristic-zero assumption with the appropriate
finite-module consequences). `PrimeField.lean` already has
`[Module.Free ℤ_[p] A]` from E3, so the restricted FLT route needs no new
arithmetic premise to make this repair. Merely adding a domain instance does
not fix it; the source already has one.

**Separate hypothesis mismatch:** blueprint lines 193–198 assume that the residual representation
is irreducible. `mem_isCompatible` does not. Its conclusion is equality of
representations with its p-adic member, not merely equality of traces.
The blueprint route therefore does not prove its exact general signature
without an additional reducible-case argument. The actual caller retains
`hirr` and a reduction isomorphism, so pass that witness into a restricted
companion theorem. A domain quotient preserves the particular reduction, but
one still has to carry its tensor associativity/equivariance proof.

A second caution: the full Lean family is indexed at **every prime**, even
2; only its HR clause is restricted to odd primes. The two-member interface
avoids constructing an unnecessary 2-adic family member.

### Concrete weaker contract

For a finite free domain p-adic model `σ : GaloisRep ℚ A W`, use proposed
`TraceCompanion3 σ`, with the following fields (a dependent record will
register the listed structures as instances):

```lean
-- Proposed record signature; coefficient instances are part of its data.
structure TraceCompanion3 (σ : GaloisRep ℚ A W) where
  E : Type
  fieldE : Field E
  numberFieldE : NumberField E
  B : Type
  -- B is a commutative local domain, finite free over ℤ_[3],
  -- with topological ring and IsModuleTopology ℤ_[3] B instances.
  U : Type
  -- U is a finite free B-module, of rank two.
  η : GaloisRep ℚ B U
  hardly : IsHardlyRamified (by decide : Odd 3) hU η
  iA : A →+* AlgebraicClosure ℚ_[p]
  iB : B →+* AlgebraicClosure ℚ_[3]
  ψ : E →+* AlgebraicClosure ℚ_[p]
  φ : E →+* AlgebraicClosure ℚ_[3]
  S : Finset (HeightOneSpectrum (𝓞 ℚ))
  a : ℕ → E
  trace_p : ∀ q (hq : q.Prime), 5 ≤ q → q ≠ p →
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    iA (frobTrace σ q hq) = ψ (a q)
  trace_3 : ∀ q (hq : q.Prime), 5 ≤ q →
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    iB (frobTrace η q hq) = φ (a q)
```

This is a record **specification**, not compilable Lean as printed: replace
instance comments with explicit dependent fields, including the rank proof
`hU`. Ring maps suffice for the scalar trace equalities; one need not assert
an isomorphism between the two representations in different characteristics.
Injectivity of `iA` follows from E4; that of `φ` from its field domain.
From T's trace result, `φ(a q) = φ(1+q)` implies `a q = 1+q`, then `iA`
reflects the p-adic trace equality. No purity theorem or Frobenius eigenvalue
comparison is needed in this algebraic adapter.

### Leaves

**F0 — two-embedding trace transfer. S; now.**

```lean
theorem trace_scalar_transfer [Field E] [CommRing A]
    [Field Kp] [Field K3] (ψ : E →+* Kp) (φ : E →+* K3)
    (iA : A →+* Kp) (hi : Function.Injective iA)
    (iB : B →+* K3) (a : E) (x : A) (y : B) (q : ℕ)
    (hx : iA x = ψ a) (hy : iB y = φ a) (ht : y = 1 + q) :
    x = 1 + q
```

Include `[CommRing B]`. Apply `φ.injective`, map `1+q`, then `hi`.
Dependencies: basic ring maps only; E5 is the existing model for the proof.
Acceptance: no `mem_isCompatible`, `three_adic`, or other arithmetic admission.
This is **actually small** and reusable independent of the companion record.

**F1 — extract a companion from the current full-family output. S–M;
cap the extraction now.**

```lean
theorem traceCompanion3_of_full_family
    (data : FullFamilyWitness σ) : Nonempty (TraceCompanion3 σ)
```

`FullFamilyWitness σ` means the entire *conclusion* of `mem_isCompatible`
quoted above, supplied as a hypothesis, not a new theorem proving it. Choose
one embedding into `ℚ₃`-bar, use the integral model there, and take
`a q = -(Pv vq).coeff 1`; prove E5's coefficient identities. Dependencies:
E4/E5, `IsAlgClosed.lift`, and the record definition. No arithmetic is closed;
it proves the proposed interface really is implied by the old one. Only
combine with a new existence theorem when that theorem is proved.

**F2 — retain residual irreducibility through the domain quotient. M; no
until tensor bookkeeping is split into a smaller statement.**

```lean
theorem residual_iso_after_domain_quotient
    (e : k ⊗[R] W ≃ₗ[k] V) (he : (σ.baseChange k).conj e = ρbar)
    (hRA : Function.Surjective (algebraMap R A)) :
    ∃ eA : k ⊗[A] (A ⊗[R] W) ≃ₗ[k] V,
      ((σ.baseChange A).baseChange k).conj eA = ρbar
```

Inherit E3's compatible `R → A → k` algebras and continuous scalar actions.
E3 constructs the coefficient map, not this named reduction-isomorphism
lemma. Tensor associativity and the existing base-change/conjugation APIs
should prove it. Then transport `hirr` along the displayed equality. With
a domain lift returned directly by L6, this leaf is unnecessary.

**F3 — potential modularity with controlled places. XL; no.**

```lean
theorem exists_potential_modularity_data
    (hσ : HR σ) (hr : IrreducibleResidualModel σ) :
    Nonempty (PotentialModularityData σ)
```

Proposed input `IrreducibleResidualModel` consists of a finite residue field,
a reduction map/isomorphism and an irreducible residual representation.
The output must specify a totally real finite extension, local splitting
conditions at the bad places, an actual weight-two automorphic eigenform,
and an isomorphism with the restricted generic fibre. It must provide the
extension properties needed for F5, not just an arbitrary modular extension.
Dependencies: shared seed A0 below, local deformation theory L1/L2,
and the modularity-lifting comparison constructed in L4 over auxiliary fields. E12 is only the algebraic
patching endgame. Mathlib alone does not supply this theorem.

**F4a — Galois representations attached at good primes. XL; no.**
First prove the existing `exists_galoisRep_isAttachedAtGoodPrimes` E15
for an arbitrary automorphic form in the needed weight-two setting. This
attachment theorem is independent of F3 and L6. Apply it to F3's form to
give p and 3 representations with common Frobenius traces. Lean acceptance:

```lean
theorem attached_pair_of_potential_modularity
    (d : PotentialModularityData σ) : Nonempty (AttachedPairData d p 3)
```

`AttachedPairData` contains genuine representations over the auxiliary field,
coefficient embeddings, finite exceptional set and the two trace equalities.
Dependencies: automorphic forms/Hecke eigenvalues and etale cohomology of
appropriate Shimura curves. Existing forms and E15's predicates help; its
existence theorems are admitted. Do not substitute the similarly named
conditional adapter `isAutomorphicOfLevel_of_isAttachedAtGoodPrimes`.

**F4b — integral 3-adic local properties. XL; no.**
Prove the three separate existing E15 integral/tame/flat model outputs in the
required setting, and show **one common model** has all three properties.

```lean
theorem attached_three_adic_hardly_model
    (d : AttachedPairData pm p 3) : Nonempty (IntegralHardlyModel3 d)
```

Output a finite free coefficient **domain**, lattice, HR proof, and generic
fibre comparison. Existence of unrelated good lattices for separate local
conditions does not suffice. Dependencies: F4a, local-global compatibility,
finite-flat integral models, T2-style lattice transport; E9/E15 are the
interfaces. The map at 2 has to satisfy the actual E1 quotient equation.

**F5 — descent of the pair to `ℚ`. XL; no.**

```lean
theorem descend_attached_pair
    (d : PotentialModularityData σ) (pair : AttachedPairData d p 3)
    (int3 : IntegralHardlyModel3 pair) : Nonempty (TraceCompanion3 σ)
```

Use solvable base change/Brauer induction and irreducibility to turn descent
identities into actual two-dimensional representations; show traces and
local conditions descend. Dependencies: F3/F4, E16's currently admitted
base-change/induction inputs, finite-group induction and descent theory.
A virtual character with the right Frobenius values is not the output.

**F6 — B5 assembly with the restricted companion. S; after T and L/F5.**
Replace the full-family extraction/`compatible_trace` part of `PrimeField`
by F0, T0 and residual trace descent E4. Preserve the existing result
`¬ ρbar.IsIrreducible`, without any extra hypothesis at the public endpoint.
The cap is reasonable once the witness record and arithmetic theorems compile.
It is not dispatchable as an unconditional proof today.

**F7 — repaired general `mem_isCompatible`. XL/unpriced; defer.**
First add the missing characteristic-zero/torsion-free coefficient condition;
the exact quoted statement cannot be proved soundly as it stands. For a
corrected general theorem, add all other primes, including 2, and treat reducible input representations
or prove their traces have the required algebraicity/classification. Ensure
the p-adic member is the actual representation as stated. A system only for
residually irreducible inputs proves the restricted theorem, not the corrected general one.
The plan recommends taking this excess generality off the FLT path.

## L: lifting the residual representation

### Mathematical route and restriction

The target is not merely a universal deformation ring. It asserts a
characteristic-zero, finite free coefficient point satisfying **all** HR local
conditions and reducing to the given representation. A universal ring can
have no characteristic-zero points at all; formal smoothness of separate
local problems does not solve the global problem.

The standard route uses a fixed-determinant minimal/flat deformation problem,
local deformation-ring geometry, a global Selmer/dual-Selmer dimension
calculation, potential modularity and arithmetic patching to obtain finiteness,
and a positive-characteristic-zero-dimension/nonvanishing argument to extract
a point. References: Khare–Wintenberger II as above for the lifting method;
Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Ann. of Math. 141
(1995), 443–551; Taylor–Wiles, *Ring-theoretic properties of certain Hecke
algebras*, same volume, 553–572. These references explain the method; a worker
must match the finite-flat local condition, quotient at 2 and exceptional
residual images, rather than importing a generic “R=T”.

Only prime-field residues with `p ≥ 5` reach the current caller. Returning a
domain lift over `ZMod p` avoids the quotient step, and a specified reduction
witness supports the restricted F3 theorem. Restricting further to `p ≥ 17`
removes small residue primes, but not all exceptional-image issues required
by a modularity-lifting theorem.

For L below, `DomainLift ρbar` denotes exactly the existential data in
`lifts`, with `[IsDomain R]` added. Thus it includes a local finite free
`ℤ_[p]`-algebra with its module topology, compatible algebra to `ZMod p`, a
rank-two free representation, HR, and an actual equivariant reduction
isomorphism. This is an explicit output contract, not an assumption that a
lift already exists.

### Leaves

**L0 — absolute irreducibility adapter. M; cap a linear-algebra subleaf now.**

```lean
theorem absIrred_of_rank_one_fixed_space
    (hirr : ρbar.IsIrreducible)
    (hc : Module.finrank k (Module.End.eigenspace (ρbar c) 1) = 1) :
    Representation.IsAbsolutelyIrreducible ρbar.toRepresentation
```

Use E17 for every extension field, then package the class E10 expects.
The general adapter is **S, now**, subject to the exact GaloisRep coercions;
its input includes `hc`. Supplying `hc` from HR requires complex conjugation,
`c² = 1`, `det ρbar(c) = -1`, and characteristic not 2. Those global/cyclotomic
interfaces are a separate M leaf. Do not redispatch E17's Burnside proof.
The fixed-space computation for a 2×2 involution with determinant −1 is
another bounded algebra leaf; it does not construct complex conjugation.

**L1 — the actual restricted deformation functor. L–XL; no.**

```lean
theorem hardlyDeformationFunctor_corepresentable
    (hirr : ρbar.IsIrreducible) (hρ : HR ρbar) :
    (hardlyDeformationFunctor ρbar).IsCorepresentable
```

Define framed lifts modulo strict equivalence with fixed cyclotomic
determinant, no new ramification, finite-flatness at p and the precise
rank-one quotient condition at 2. Verify closedness/representability of these
conditions rather than replacing the quotient at 2 by a trace condition
without proof. Dependencies: L0, E9/E10, E11's functor infrastructure. The
narrow functor's own representability is admitted and has different field
hypotheses. Mathlib categories/local algebra and Witt vectors are foundations.

**L2 — local deformation-ring geometry. XL; no.**

```lean
theorem local_hardly_deformation_geometry (hρ : HR ρbar) :
    Nonempty (LocalDeformationGeometry ρbar)
```

The proposed output records local rings at p and 2, their representing
properties, nonempty characteristic-zero components of the required type,
dimension/lifting bounds, and tangent-space subspaces in actual continuous
cohomology. Include the two possible unramified quadratic quotients at 2.
Dependencies: L1 local components, finite-flat deformation theory and
ramification geometry. E9's finite-flat closure is useful but does not give
these dimension bounds. Refine this XL task into the p-local and 2-local
problems once coefficient and framing conventions are fixed.

**L3 — global deformation presentation and dimension bound. XL; no.**

```lean
theorem global_hardly_deformation_lower_bound
    (localData : LocalDeformationGeometry ρbar) :
    Nonempty (GlobalDeformationPresentation ρbar localData)
```

The output is a presentation of the global ring over the chosen local rings,
with generator/relation counts from Selmer and dual Selmer groups and a
verified lower bound strong enough for L5. Dependencies: L1/L2, arithmetic
Poitou–Tate/local duality, Euler characteristic and cohomology finiteness.
E13 supplies only a carrier/order-formula contract; actually construct its
Galois realization. E14 and Mathlib group cohomology help with complexes,
not with that arithmetic realization.

**L4 — finiteness and nonvanishing from arithmetic patching. XL; no.**

```lean
theorem global_hardly_deformation_finite
    (pres : GlobalDeformationPresentation ρbar localData) :
    Module.Finite ℤ_[p] (HardlyDeformationRing ρbar)
```

Construct the potential-modularity comparison over auxiliary totally real
fields, nonzero localized automorphic modules, auxiliary Taylor–Wiles primes
and control maps, with hypotheses sufficient to instantiate E12. Control
restriction/descent back to the global ring. Dependencies: L2/L3, the independent residual modular seed A0 below,
the general attachment theorem in F4a, and arithmetic patching. This
construction does not assume F3 or the existence of the global lift L6. A nilpotent-kernel conclusion by itself neither proves finiteness
without finite target data nor proves the characteristic-zero fibre nonzero.
This is the largest shared L/F development, not an independent cheap use of
`ker_RtoT_le_nilradical`.

**L5 — extract a characteristic-zero point. M–L; after L3/L4.**

```lean
theorem exists_finite_domain_point
    [CommRing D] [IsLocalRing D] [Algebra ℤ_[p] D]
    [Module.Finite ℤ_[p] D]
    (hgeneric : Nontrivial (Localization.Away (p : D))) :
    ∃ P : Ideal D, P.IsPrime ∧ (p : D) ∉ P
```

First obtain a prime avoiding p from the nonzero generic fibre. Then show
`D ⧸ P` is a finite torsion-free, hence free, local `ℤ_[p]`-algebra and that
its residue reduction is the required one. Add topology and continuous
representation specialization. Proving `hgeneric` from L3/L4 is part of the
arithmetic job, not a new assumption allowed at the final endpoint. E3 already
contains related minimal-prime/free-quotient algebra; reuse it where its
stronger finite-free input is available. This row includes the extraction
and packaging, so it is not S even if the displayed prime-existence lemma is.

**L6 — specialize the universal representation. S–M; after L1–L5.**

```lean
theorem lifts_primeField_domain (hp5 : 5 ≤ p)
    (hirr : ρbar.IsIrreducible) (hρ : HR ρbar) :
    Nonempty (DomainLift ρbar)
```

Evaluate the universal representation at the constructed domain point;
transport local conditions, rank and the reduction isomorphism. Dependencies:
L1–L5, E3/E4, existing frame/unframe APIs. This is the replacement used by F6;
it may be one capped assembly job once the arithmetic contracts are stable.

**L7 — full `lifts` generality. L–XL extra; no; defer.**
The exact theorem covers all odd primes (including 3), arbitrary finite
residue fields, arbitrary module universes and the specified coefficient
algebras. Generalize L1–L6 or supply the separate small-prime/residue-field
arguments. Proving only `lifts_primeField_domain` removes this admission from
the FLT dependency path after rewiring but does not prove the old theorem.

### Avoiding lift/family existence altogether

A theorem that every irreducible odd mod-p representation of this type is
modular of weight 2 and level 2, followed by `S₂(Γ₀(2)) = 0`, would replace
L/F/T simultaneously. This is the relevant special case of Serre's modularity
conjecture (Khare–Wintenberger), not a smaller theorem already in Mathlib.
The modularity-to-level/weight bridge and level-two vanishing are separate
obligations. The latter might become a small analytic leaf after a general
valence/dimension formula at that level exists; the checked Mathlib only
provides level-one dimension endpoints. Do not label it capped today.

The classical Frey-specific route through semistable modularity and Ribet
level lowering is also valid mathematically. It replaces the same missing
modern arithmetic by different large missing arithmetic, and generally
retains Mazur for irreducibility. Constructing the ordinary p-adic Tate module
of the Frey curve does **not** bypass the hard lift: at multiplicative p it
need not satisfy this all-open-ideal finite-flat condition, and at other bad
primes the characteristic-zero Tate module retains ramification that its
mod-p representation can lose.

## M: Mazur, restricted to the used torsion orders

### What is really needed

The exact consumed exclusion, already named `mazur_W`, is:

```lean
theorem mazur_W (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point,
      Function.Injective f
```

Proving it directly avoids the full bound and the torsion-finiteness
conjunct. Another sufficient replacement is

```lean
def NoLargePrimeTorsion : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → 17 ≤ ℓ →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ¬ ∃ P : (E⁄ℚ).Point, addOrderOf P = ℓ
```

This is stronger than the required exclusion because it does not require
full two-torsion, but weaker than Mazur's full classification. It also omits
the unused primes 11 and 13 in `mazur_W_ge11`. Do not replace the axiom with
that existing sorried theorem and claim progress in trust.

`FreyPackage.mazurW_counterexample_of_reducible` produces either the original
Frey curve or a curve obtained by quotienting its stable p-line. Thus “Mazur
only for Frey curves” is not enough for the present proof. One can preserve
an explicit witness saying the curve is one of these odd-isogenous quotients
and formulate the exclusion only for that class. The current exported
counterexample theorem forgets that provenance; change its witness if pursuing
this route. No elementary torsion theorem for that class was located. Proving
its exclusion by assuming FLT/no Frey packages would be circular.

### Mathematical route

For the full axiom, Mazur's *Modular curves and the Eisenstein ideal*, Publ.
Math. IHÉS 47 (1977), 33–186, DOI `10.1007/BF02684339`, proves the torsion
classification: cyclic orders 1–10 or 12, or `Z/2 × Z/(2m)` with `1 ≤ m ≤ 4`.
Finiteness plus the elementary cardinal bound 16 then proves the axiom.
For the recommended narrower route, extract only the exclusion of rational
points of prime order ≥17 (or full-two-torsion with such a point). Translate
rational torsion into a noncuspidal point of the relevant modular curve;
use the Eisenstein quotient, its rational-point/finite-flat group-scheme
control and formal immersion/cuspidal analysis to rule it out. Pin the
specific prime-level argument in the paper before formalizing; the global
classification theorem is a valid reference, not a ready formal leaf.

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves* (1985), supplies modular
curve integral models and degenerations. Silverman, *The Arithmetic of
Elliptic Curves*, supplies torsion reduction and isogeny background. Neither
Lutz–Nagell nor Mordell–Weil alone gives the uniform bound as E varies.
Reducing at one convenient good prime cannot be assumed uniformly for all
Frey packages and their quotient curves. Avoid replacing the prime-level
Eisenstein method by the much larger modern nonvanishing machinery merely
to obtain this prime-order corollary.

### Leaves

**M0 — prime-torsion exclusion implies W. S; now.**

```lean
theorem mazur_W_of_noLargePrimeTorsion (h : NoLargePrimeTorsion)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point,
      Function.Injective f
```

Restrict f to the last factor and take the image of 1. Injectivity preserves
its additive order ℓ. Dependencies: E23 only, plus curve point instances.
No cardinality of the ambient torsion subgroup is involved. The hypothesis
is explicit; this is not an unconditional replacement proof.

**M1 — cardinality interface generalization. S; now, optional.**

```lean
theorem no_fullTwoTimesPrime_of_torsion_bound
    {A : Type*} [AddCommGroup A] (ℓ B : ℕ) [NeZero ℓ]
    (hfin : Finite (AddCommGroup.torsion A))
    (hb : (AddCommGroup.torsion A : Set A).ncard ≤ B)
    (hlt : B < 4 * ℓ) :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ A, Function.Injective f
```

Generalize the existing proof of `mazur_W`; E23 and `Set.ncard_le_ncard`.
It shows the caller only needs a bound below `4ℓ` for its particular curve.
Keep `hfin`: `ncard` of an infinite set is zero. This does not remove Mazur
unless an independent bound is obtained, and is lower priority than M0.

**M2 — prime-level torsion/moduli bridge. XL; no.**

```lean
theorem pointOfOrder_to_modularPoint
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = ℓ) :
    Nonempty (NoncuspidalRationalPoint (X1 ℓ))
```

Construct `X1 ℓ` with its moduli interpretation and compactification, and
prove that an exact-order rational point determines a noncuspidal rational
moduli point. An alternative full-two-torsion route uses its appropriate
mixed-level curve, not automatically `X1 ℓ`. Dependencies: elliptic-curve
level structures, schemes/moduli/compactification. E24 supplies point and
scheme foundations, not these modular curves. A bridge to a **newly assumed**
moduli interpretation cannot be counted as this theorem's completion.

**M3 — integral modular-curve and Eisenstein quotient machinery. XL; no.**

```lean
theorem eisenstein_prime_level_data (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ) :
    Nonempty (EisensteinPrimeLevelData ℓ)
```

Specify actual modular Jacobian and Eisenstein quotient, Hecke action,
cuspidal subgroup, integral models and maps, and the rational-point/control
properties the next leaf will use. These cannot be unproved fields filled
by assumptions. Dependencies: M2 geometric foundation, Jacobian varieties,
Hecke correspondences, finite-flat group schemes and cohomology. E20 is
mostly admitted; E24's Jacobian coordinates do not supply these varieties.
This is the largest Mazur work package and needs a source-level subplan.

**M4 — noncuspidal rational point exclusion. XL; no.**

```lean
theorem no_nonCuspidal_X1_largePrime
    (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ) :
    IsEmpty (NoncuspidalRationalPoint (X1 ℓ))
```

Prove the needed prime-level consequence using M3's actual arithmetic:
formal immersion at relevant cusps, reduction/specialization of rational
points, and the Eisenstein quotient's rational points. Handle exceptional
prime-level cases identified by the paper separately. Depends on M3; a list
of numerical checks at small primes does not cover all ℓ≥17. This statement
is the precise narrower arithmetic goal, not a claimed general theorem
that genus greater than one implies no rational points.

**M5 — restricted Mazur assembly. S; after M2/M4.**
Derive `NoLargePrimeTorsion` using M2/M4; apply M0 to reprove `mazur_W`.
Keep `FreyPackage.mazur` unchanged. This removes `Mazur_statement` from the
FLT path if all those dependencies have clean axiom audits. It does not
prove or delete the full axiom elsewhere.

**M6 — full torsion classification and cardinality. XL extra; defer.**
To prove `Mazur_statement` itself, supply the remaining small-prime and
prime-power exclusions and mixed torsion cases, as well as torsion finiteness.
The finishing leaf, **S after the classification**, has acceptance

```lean
theorem torsion_bound_of_classification (h : MazurTorsionClassification E) :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) ∧
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

`MazurTorsionClassification E` must contain an actual additive equivalence
between the torsion group and one of the finite allowed groups, not just a
cardinality disjunction. E23 handles the final arithmetic; the classification
is new work. It is unnecessary for the FLT consumer.

## Shared arithmetic and dependency graph

**A0 — residual potential-modularity seed. XL; no.** Separate this from
potential modularity of the *particular* characteristic-zero lift in F3.

```lean
theorem exists_residual_modular_seed
    (hirr : ρbar.IsIrreducible) (hρ : HR ρbar) :
    Nonempty (ResidualModularSeed ρbar)
```

The output specifies an auxiliary totally real extension with required local
behavior and a genuine automorphic characteristic-zero representation whose
residual representation agrees with `ρbar` restricted there. Construct via
potential-modularity/moduli realization methods and the required starting
modularity results; prove them, do not introduce an opaque existence axiom.
It does **not** assert the desired HR characteristic-zero lift over `ℚ`.
Dependencies: L0, moduli/local realization, attachment F4a as an independent
theorem about automorphic forms, and the necessary initial automorphy input.
Mathlib has no such seed theorem. The Moret–Bailly and automorphy ingredients
must be source-matched in the first arithmetic design pass.

This separates an otherwise circular proposed proof: use the residual seed
to build the deformation comparison, then obtain the global lift, then prove
that this particular lift is potentially modular and has companions. Do not
use the existence of the desired lift as an input to proving that it exists.

```text
L0 + local/moduli seed A0 + general attachment F4a
   + local deformation geometry L1/L2 + arithmetic duality L3
   → arithmetic patching/comparison L4
   → point extraction L5 → domain lift L6
   → potential modularity of this lift F3
   → attached pair F4a + integral local models F4b
   → descent F5 → TraceCompanion3

T3a (Fontaine bound) + E8 + residual classification T3b
   + stable lattice transport T2 → Ribet obstruction T4a
   + rank-one classification T4b → domain three-adic trace

L6 + F5 + domain three-adic trace + F0 + existing E4/E6
   → restricted B5 (F6) → B4

M2 (modular-curve interpretation) → M3 (Eisenstein arithmetic)
   → M4 (prime-level exclusion) → M5/M0 → mazur_W
   → FreyPackage.mazur

B4 + FreyPackage.mazur → B3 → B2 → B1 → FLT
```

The input hypotheses in each shared theorem must be made compatible; this is
not a proof that an arbitrary available version of potential modularity and
an arbitrary available version of modularity lifting compose. In particular,
auxiliary-field splitting, residual-image exceptions and integral local types
are acceptance conditions. If matching them changes the route, revise the XL
contracts before launching implementation, not after generating placeholder
Lean definitions.

## Total scope and what to dispatch

The table estimates **new Lean development**, excluding the checked-out
foundations and avoiding counting the shared L/F work twice. These are broad
expert judgments with substantial uncertainty, not calibrated deadlines.

| Route/workstream | Rough new proof lines | Engineering scale | Capped endpoint today? |
|---|---:|---|---|
| T2–T4: domain-only three-adic theorem, including mod-3 arithmetic | 8,000–25,000 | Many expert-months; roughly 0.5–2 person-years | No |
| A0/L1–L6/F3–F5: shared lifting, potential modularity, attachment and p/3 descent | 40,000–150,000 | Several expert-years; roughly 3–12 person-years | No |
| M2–M5: prime-torsion exclusion without full torsion classification | 20,000–80,000 | Several expert-years; roughly 2–8 person-years | No |
| Bounded adapters and final assembly | 300–1,500 | Days to weeks once inputs exist | Some adapters only |
| **Recommended restricted path total** | **about 70,000–260,000** | **roughly 6–22 expert person-years, with no reliable upper bound** | **No arithmetic endpoint** |

These estimates reflect missing mathematical libraries, not the count of
`sorry` tokens. Parallel experts may reduce elapsed time, but the dependencies
and review burden prevent linear speedup. Matching precise literature
hypotheses or discovering more useful proved infrastructure could change the
ranges materially. The unrestricted strengthenings T6/L7, a **corrected** general-family
statement F7, and the full Mazur classification M6 are **additional unpriced
work**. The present F statement has a counterexample, so no sound estimate
can promise to prove all four exact signatures unchanged. The table must
not be presented as the cost of proving all four exact statements unchanged.
A direct Serre-modularity or semistable-modularity route is also research-scale;
this source audit does not justify a smaller total estimate for it.

### Small leaves that can be capped now

| Priority | Leaf | Cap and acceptance |
|---|---|---|
| 1 | F0, two-embedding scalar trace transfer | 1–2 hours; elementary ring-map proof, no arithmetic assumptions beyond the explicitly supplied equalities |
| 2 | M0, prime-order exclusion ⇒ W | 2–4 hours; restrict an injection to `ZMod ℓ`, preserve additive order, apply the supplied exclusion |
| 3 | T1's triangular 2×2 matrix trace/determinant lemma | ≤2 hours; direct matrix calculation; general quotient/basis version may require an M follow-up |
| 4 | L0's fixed-space ⇒ absolute-irreducibility class adapter | 2–4 hours; package E17 with the fixed-space hypothesis explicit; do not include the complex-conjugation bridge in the same cap |
| 5 | T0 or F1 interface extraction | 2–4 hours each after choosing the record fields; prove a conditional adapter, clearly labelled as such |
| Optional | T5, equality from all power quotients | 1–2 hours; E22 wrapper, only if pursuing the quotient-congruence route |
| Optional | M1, abstract torsion cardinality exclusion | 1–2 hours; generalize the already present W proof, without removing finiteness |

Prefer F0/M0/T1 first. They have concrete standalone statements and independent
acceptance checks. Do not spend repeated caps on the giant arithmetic leaves
or on declaring records whose fields merely restate the missing theorems.
The next useful research assignment is a bounded paper/API audit of T3b and
the T2/T4 lattice route, ending in a source-matched proof outline and a list
of exact missing local lemmas; it should not promise to prove `three_adic`.

### What can be avoided, and what cannot

* The **full `Mazur_statement`** can be removed from this dependency path by
  proving W or its prime-order sufficient condition. No full classification,
  cardinality bound or finiteness theorem is needed by the revised consumer.
  Arithmetic torsion exclusion remains; quotient curves must be covered.
* The **all-primes/all-inputs `mem_isCompatible`** can be removed by proving
  F5 only for characteristic-zero lifts with the carried residual
  irreducibility witness. The old statement must also be repaired because
  its coefficient hypotheses allow positive characteristic. The existence of a suitable 3-adic companion remains deep.
* The **nonreduced-ring `three_adic`** can be removed in favor of the domain
  trace theorem, or the trace after the chosen embedding. The domain theorem
  still needs Fontaine/mod-3 and characteristic-zero arguments.
* The **all-finite-fields/all-odd-primes `lifts`** can be removed in favor of
  L6 for `ZMod p`, p≥5 (or ≥17 at a restricted B5 endpoint). A genuine
  characteristic-zero HR point is still required. No direct Tate-module
  substitution has been justified.
* Replacing all three Galois inputs by the level-two case of Serre modularity
  avoids those names but replaces their research program; it is not proof
  elimination. None of the four underlying arithmetic requirements has an
  established elementary bypass in the inspected code.

## Reproducible checks and future acceptance

Read-only commands used for the source inventory (run from the repo root):

```bash
git rev-parse HEAD
git -C .lake/packages/mathlib rev-parse HEAD
rg -n 'three_adic|mem_isCompatible|Mazur_statement|mazur_W|\.lifts\b' \
  FLT FermatsLastTheorem.lean --glob '*.lean'
rg -n 'not_isIrreducible_of_prime_field|torsion_not_isIrreducible|\.mazur\b|B[1-4]_proof' \
  FLT --glob '*.lean'
rg -n '\bsorry\b|^axiom' FLT/GaloisRepresentation/HardlyRamified/{Threeadic,Family,Lift,ModThree}.lean \
  FLT/GaloisRepresentation/{Attachment,Automorphic}.lean FLT/Deformations/Representable.lean \
  FLT/MazurChapter/AdmissibleGroupSchemes.lean
rg -n 'Fontaine|Ribet|Eisenstein ideal|crystalline|Mazur' \
  .lake/packages/mathlib/Mathlib/NumberTheory \
  .lake/packages/mathlib/Mathlib/AlgebraicGeometry
rg -n 'orderFormula|greenbergWilesOrderFormula' FLT/PoitouTate.lean
rg -n 'ker_RtoT_le_nilradical' FLT/Patching/REqualsT.lean
rg -n 'hardly_ramified_lifts|hardly_ramified_spreads_out|hardly_ramified_3adic_reducible|Fontaine' \
  blueprint/src/chapter/ch03freyreduction.tex
```

Search is evidence for names/use sites; it is not a kernel dependency audit
and can miss unfamiliar terminology. Source locations above are relative to
the recorded commit. Proposed identifiers have no “existing” status.

After each implementation leaf, elaborate that leaf in a built worktree,
check its exact type and print its axioms. For the three Galois replacements,
print axioms of the revised prime-field endpoint before claiming the B5
admissions have gone. For Mazur, audit `mazur_W` and `FreyPackage.mazur`.
Finally print `#print axioms PNat.pow_add_pow_ne_pow`: no new assumption or
`sorryAx` may replace the old one invisibly. Removing a theorem from the
active path is a valid FLT improvement but must not be reported as proving
its stronger old signature. No such proof or axiom-removal claim is made by
this document.
