# Three-adic lattice plan after the Ribet port

> Historical inventory: the tables below describe the 18:04 UTC snapshot, not
> the current implementation. For the consolidation checkpoint and runnable axiom
> checks, see [CORE_PLAN.md](CORE_PLAN.md#integration-checkpoint--2026-09-27)
> and `FLTTest/ThreeAdicConsolidation.lean`. In particular, normalization,
> lattice transfer, residual characteristic, and the specialized quadratic
> exclusion now have implementations; the arithmetic endpoints remain open.


Checked at **2026-09-27 18:04 UTC** against worktree HEAD
`2502634916a27d7e1ef09728ac046fdce1dd4f55`, local `origin/main`
`71deb063db82a8ffc6842760516626920510dd3c`, and Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76` [E1]. This is a **source audit**:
no Lean changes, builds, elaboration, or fresh `#print axioms` checks.
“Supplied” below means the stated declaration has a proof body in this
snapshot, not that this audit independently certified its transitive axioms.
Evidence tags resolve to reproducible commands in §7. Proposed declarations
are explicitly marked; absence claims mean “not found by the scoped search
E8”, not a proof that no equivalent API exists.

The port supplies the algebraic Ribet step Q1. It supplies much of L1,
commensurability for L4, and residual semisimplification independence, but
neither continuous HR transport nor residual classification. The new work
should start with the small interface lemmas in §5, then L0-normalization,
L1-continuity, and L3-subobjects. R5/R7/R10 remain substantial arithmetic
projects. No two-hour leaf closes `three_adic` [E2–E8].

## 1. Scope, names, and the changed dependency graph

**Resolve the L0 collision.** In `AUDIT.ref.md`, L0 means normalization of a
finite domain over `ℤ₃`. In the briefing's list of work already on main,
“L0” means the absolute-irreducibility adapter. These are different results.
Here **L0-N** denotes the audit's normalization leaf; **A0** denotes the
proved adapter. A0 does not provide any DVR, integral-closure, or topology
instance [E0, E4, E6].

The target in `GaloisRepresentation.IsHardlyRamified.mod_three` is a
**trivial quotient**, hence subcharacter `χ̄₃` and quotient character `1`.
Ribet must be applied in the opposite order, **sub `1`, quotient `χ̄₃`**.
The port's `StableLattice.IsExtensionOf ρ φ₁ φ₂` uses exactly that
sub/quotient ordering. Its `HasSemisimplification` is the disjunction of the
two extension orders, not a general semisimplification object [E2, E3].

The lattice route below treats the hypotheses of `three_adic` **plus
`IsDomain R`**. The current theorem itself does not assume a domain and is
still admitted. The family supplied to the `PrimeField.lean` consumer has a
domain coefficient ring. A domain proof can serve that consumer after
explicit integration; it does not prove the currently stronger all-ring
statement or its nilpotent coefficient directions [E2].

Revised graph (names on edges refer to leaves below):

```text
R0a characteristic ──┐
R1 models + R0b coefficient extension + R3 inertia + R4 auxiliary object
                    └→ R5 discriminant + R6 sextic arithmetic + R7 exclusion
                       + R8 [supplied] → R9 simple objects
R1 + R10 reverse Ext vanishing + R9 → R12 sorted filtration
R1 + R11 pure actions + R12 + R0a → R13 mod_three

L0-N → L1 continuous lattice/reduction bridge
L0-N + L2 normalization flatness + L3 subobjects + L1 → L4 all-lattice flatness
L1 → L5 quotient at 2; L1/L2/L4/L5 → L6 all-lattice HR
L6 + L6r quotient generalization + R13 + Q0 → residual factors + all-lattice trivial quotients
Q1 [supplied] + Q2 [supplied] + Q2-port [new S] → Q3 algebraic contradiction
Q3 + L3/L4/L6 → C0 integral characters
R1/R9/R11/R12 + C0 → C1 uniform pure finite levels
C1 + C3 [supplied] → C2a exact characters
C0 + C2a + T1/trace API → C2b domain trace → Frobenius specialization
```

Q3's algebraic conditional theorem can be implemented before R13/L6. Its
arithmetic hypotheses remain explicit. Likewise Q0 can be split into
algebraic adapters and a later arithmetic application. This prevents
importing the admitted `mod_three` into a purportedly admission-free
conditional proof. Q1 assumes ordinary irreducibility as a typeclass;
A0/absolute irreducibility is **not** a prerequisite for it [E2, E3, E4].

## 2. Complete leaf inventory

Paths in this table are relative to the repository. `HR/` abbreviates
`FLT/GaloisRepresentation/HardlyRamified/`; `Ribet/` abbreviates
`FLT/KnownIn1980s/Ribet_Lemma/`. All remaining contracts and sizes appear
in §§3–5. “Open” excludes use of an admitted endpoint as completion.

### Lattices, Ribet, and exact characters

| Audit leaf | What this snapshot supplies | Remaining work |
|---|---|---|
| L0-N | No normalization endpoint located. Mathlib `IsIntegralClosure.finite`, `IsIntegralClosure.module_free`, `IsIntegralClosure.rank`, `IsIntegralClosure.isDedekindDomain` in `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean` are ingredients [E6, E8]. | Complete DVR/topology/finite residue package; **L**. A0 is not this leaf. |
| L1 | `StableLattice.Reduction`, `StableLattice.Stabilizes`, `StableLattice.IsStableLattice`, `StableLattice.latticeRep`, `StableLattice.reductionMap`, `StableLattice.reducedRep` in `Ribet/Defs.lean`; `StableLattice.finrank_reduction` and `Submodule.IsLattice.finrank_eq` in `FLT/Slop/Ribet_Lemma/stable_lattices.lean`; `StableLattice.exists_isStableLattice_proof` in `Ribet/Proofs.lean` [E3]. | Algebraic core supplied; continuous `GaloisRep`, generic-fibre and residual base-change identifications, finite/discrete residue instances still **M** after L0-N. Existence theorem needs an **open stabilizer** hypothesis. |
| L2 | `GaloisModule.IsFiniteFlat.finPow` and `.quotient` in `FLT/GroupScheme/FiniteFlat.lean`; `GaloisRepresentation.B5Inputs.flatAt_quotient` in `HR/B5Inputs.lean` only treats a surjective coefficient map [E5]. | Finite, possibly nonflat coefficient extension to normalization; **L**. |
| L3 | `HopfAlgebra.IsFiniteFlat.quotient_comap`, `GaloisModule.GenericFiber.pullbackBialgHom`, `.pointsEquivariantAddEquiv` in `FLT/GroupScheme/FiniteFlat.lean` are ingredients [E5]. | Galois-module subobject theorem with generic-points comparison not located; **L** [E8]. |
| L4 | `Submodule.IsLattice.exists_smul_le`, `.smul_of_ne_zero`, `StableLattice.Stabilizes.smul`, `StableLattice.reducedRep_smul_equiv` in `FLT/Slop/Ribet_Lemma/stable_lattices.lean` [E3]. | Commensurability supplied; all-open-ideal flatness of every lattice still **M** after L1–L3. |
| L5 | Port supplies `StableLattice.latticeRep`; HR's exact quotient-at-2 condition is `GaloisRepresentation.IsHardlyRamified.isTameAtTwo` in `HR/Defs.lean` [E2, E3]. | Primitive integral functional with the same local character, plus continuity; **M** after L1. |
| L6 | `GaloisRepresentation.B5Inputs.hardlyRamified_quotient` in `HR/B5Inputs.lean` handles surjective coefficient quotients **only when both coefficient rings are finite free over ℤₚ** [E5]. | All four HR clauses for arbitrary stable lattices, **M** after L0-N–L5; add **L6r S** to remove the incompatible residue-target hypothesis. |
| Q0 | `StableLattice.HasSemisimplification` in `Ribet/Defs.lean`; `StableLattice.hasSemisimplification_independent_of_lattice_proof` in `Ribet/Proofs.lean`; `StableLattice.IsExtensionOf.congr`, `StableLattice.HasSemisimplification.congr`, `StableLattice.HasSemisimplification.symm`, `StableLattice.exists_character_of_stable_line` in `FLT/Slop/Ribet_Lemma/Brauer_Nesbitt.lean` [E3]. | Independence supplied; obtaining `χ̄₃,1` from an HR trivial quotient, determinant and distinctness remains **M**. No proof of R13 is supplied by independence. |
| Q1 | **Supplied:** `StableLattice.ribet_lemma_proof` in `Ribet/Proofs.lean`, proved using `StableLattice.ribet_lemma_slop` in `FLT/Slop/Ribet_Lemma/Ribet_Lemma.lean` [E3]. | No new Ribet proof. Supply its explicit instances, `hdim`, starting lattice, and `hss`. It retains nonsplitting; no distinctness hypothesis is required by the endpoint itself. |
| Q2 | **Supplied on main:** `GaloisRepresentation.equivariant_retraction_of_trivial_quotient` and `.stable_complement_of_trivial_quotient` in `HR/ThreeAdicAlgebra.lean` [E4]. | A small interface bridge to the port's `IsSplitExtensionOf` remains: **Q2-port, S**. The existing complement theorem asserts stability, whereas the port also records the complement's character. |
| Q3 | No all-lattice contradiction endpoint located [E8]. | Conditional assembly **S after Q2-port**, with signature in §5; arithmetic application **M** after L6/L6r/R13/Q0. |
| C0 | `StableLattice.exists_character_of_stable_line` supplies an algebraic field-valued character in `FLT/Slop/Ribet_Lemma/Brauer_Nesbitt.lean` [E3]. | Integral rank-one lattice and quotient, continuity, finite-flat levels and unramifiedness at 2 remain **M** (budget can grow to L with module/topology work). |
| C1 | No pure-level character classification located; neither Ribet nor Brauer–Nesbitt concerns higher congruences [E3, E8]. | **L** after residual/finite-flat work; **XL** for an independent Fontaine B development. |
| C2 | `GaloisRepresentation.B5Inputs.trace_baseChange_conj`, `.padic_domain_map_injective` in `HR/B5Inputs.lean`, and `.cyclotomicCharacter_adicArithFrob` in `HR/Chebotarev/FrobeniusTraces.lean` [E5, E7]. | C2a equality from uniform pure levels **S**, ready as a conditional algebra lemma; C2b exact-character/trace/embedding assembly **M** after C0/C1. |
| C3 | **Supplied on main:** root declaration `eq_of_all_power_quotients` in `FLT/Mathlib/RingTheory/AdicCompletion/PowerQuotients.lean` [E4]. | Do not redispatch. Does not produce the congruences needed by C1. |
| T1 | **Supplied on main:** `GaloisRepresentation.B5Inputs.trace_eq_one_add_det_of_matrix_trivial_quotient` and `.trace_eq_one_add_det_of_trivial_quotient` in `HR/TraceLeaves.lean` [E4]. | Reuse; no new generic “trivial quotient gives trace” leaf. |
| A0 (brief's L0) | **Supplied on main:** `Representation.absIrred_of_rank_one_fixed_space` and `GaloisRep.absIrred_of_rank_one_fixed_space` in `HR/AbsIrredAdapter.lean` [E4]. | Fixed-space input stays explicit. Off the minimal Ribet dependency path. |
| Involution input | **Supplied on main:** `Module.End.finrank_eigenspace_one_of_involution`, `.finrank_eigenspace_neg_one_of_involution` in `FLT/Mathlib/LinearAlgebra/InvolutionFixedSpace.lean` [E4]. | Applying to complex conjugation still requires square-one, determinant `−1`, and characteristic not 2; no new involution proof. |

### Residual chain (including the audit's preparatory R0)

| Leaf | Status and exact reuse | Remaining size |
|---|---|---|
| R0 | Characteristic-three endpoint not located. `PadicInt.ker_toZMod`, `PadicInt.residueField` in Mathlib `NumberTheory/Padics/RingHoms.lean` are available [E7, E8]. | Split into **R0a S** characteristic, **R0b M after R1's morphism work** coefficient action. |
| R1 | `GaloisModule.IsFiniteFlat`, `GaloisModule.GenericFiber.hopfAlgebra`, `.pointsEquivariantAddEquiv` in `FLT/GroupScheme/FiniteFlat.lean` model the local generic fibre [E5]. | Global gluing over `ℤ[1/2]` and ℤ, including morphisms: **L**. |
| R2 | **Supplied on main:** `GaloisRepresentation.cube_eq_one_of_sub_one_sq_eq_zero` in `HR/ThreeAdicAlgebra.lean` [E4]. | No work; cube-one elements do not by themselves bound the image order. |
| R3 | HR determinant/quotient fields in `HR/Defs.lean`; R2 [E2, E4]. | Square-zero inertia plus wild/tame and point-field ramification comparison: **L**. |
| R4 | `GaloisModule.IsFiniteFlat.prod` in `FLT/GroupScheme/FiniteFlat.lean`; `GaloisRepresentation.Chebotarev.exists_finiteGalois_realization` in `HR/Chebotarev/FiniteGaloisRealization.lean` [E5, E7]. | Kummer object and **augmented** point field, not just `ker ρ`: **L**. |
| R5 | `Odlyzko.not_discriminant_le_fontaine_bound` in `FLT/Odlyzko.lean` is the numerical obstruction, not the finite-flat upper bound [E7]. | Fontaine/local-to-global upper bound: **XL**. |
| R6 | No sextic-field arithmetic package located [E8]. | Degree 6, class number 1, local residue/unit and ramification certificates: **L**. |
| R7 | No quadratic auxiliary-field exclusion endpoint located [E8]. | **L**, with **XL** general reciprocity dependency unless replaced by a proved specialized Kummer calculation. |
| R8 | **Supplied on main:** root declaration `auxiliary_degree_eq_six_or_twelve` in `HR/ThreeAdicDegree.lean` [E4]. | Explicit total-complexity, degree-divisibility and discriminant inputs remain R4–R6. |
| R9 | Port's Brauer–Nesbitt theorem only compares already specified characters, and does not classify simple finite-flat objects [E3]. | Simple objects `ℤ/3`, `μ₃`: **L** after R4–R8 and model uniqueness. |
| R10 | `FLT.MazurChapter.constantOrderPrime`, `.multiplicativeOrderPrime`, `.admissible_subobject_quotient` in `FLT/MazurChapter/AdmissibleGroupSchemes.lean` still contain admissions [E7]. | Global reverse Ext vanishing: **XL**; the scaffold does not close it. |
| R11 | `NumberField.InertiaComparison.intermediateField_eq_bot_of_localInertia` in `FLT/FreyCurve/Serre/UnramifiedCharacter.lean` is reusable. `GaloisRep.trivial_of_everywhere_unramified` there has `ZMod p` coefficients [E7]. | Pure constant/diagonalizable finite levels: **L**. |
| R12 | No sorted finite-flat filtration endpoint located [E8]. | Functorial sorting using R9/R10 and subquotients: **L**. |
| R13 | `GaloisRepresentation.IsHardlyRamified.mod_three` in `HR/ModThree.lean` is still admitted. `Algebra.traceForm_nondegenerate` in Mathlib `RingTheory/Trace/Basic.lean` is a coefficient-descent ingredient [E2, E7]. | Exact invariant **k-linear** quotient: **M after R0/R1/R11/R12**, not ready. |

## 3. Remaining lattice and character contracts

Only §5 contains pasteable signatures with existing vocabulary. This section
uses **proposed** names in namespace `ThreeAdicPlan` and schematic records;
it specifies mathematics and boundaries, not elaborated Lean. Unqualified
proposed dependency names below mean `ThreeAdicPlan.<name>`. Estimates:
**S ≤2 hours for one capped worker; M several sessions/days; L weeks;
XL substantial new arithmetic/library work.** Shared prerequisites mean
these estimates must not be added as independent durations.

Conventions: `Γ = Field.absoluteGaloisGroup ℚ`; `χ₃ : Γ →* Oˣ` is the
coefficient image of the 3-adic cyclotomic character; `χ̄₃` its residue
character. `HR ρ` abbreviates **the existing**
`GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hdim ρ`,
including its ring/topology/module hypotheses. It is used only in rank two.
`ρK = ρ.baseChange K`, `W = K ⊗[R] V`, and `ρΛ`/`ρbarΛ` mean the
continuous representations whose construction is L1. A proposed record
must store the models/maps in its name, not the desired classification.

### L0-N — normalization, L

```lean
-- Inherit three_adic's coefficient hypotheses and add [IsDomain R].
-- N includes the induced Algebra ℚ_[3] (FractionRing R).
def NormalizedOrderData (R : Type*) :=
  -- K = FractionRing R; O = integralClosure ℤ_[3] K;
  -- compatible maps ℤ_[3] → R → O → K, and ℚ_[3] → K;
  -- FiniteDimensional ℚ_[3] K; IsFractionRing O K;
  -- IsDiscreteValuationRing O; IsAdicComplete (maximalIdeal O) O;
  -- Module.Finite/Free ℤ_[3] O; Finite (ResidueField O);
  -- CharP (ResidueField O) 3; standard field/module topologies;
  -- continuous coefficient maps and scalar actions for baseChange.
  ...
theorem normalization_padic_order : Nonempty (NormalizedOrderData R)
```

Dependencies: `IsIntegralClosure.finite`, `.module_free`, `.rank`,
`.isDedekindDomain` (E6); field-extension valuation/completeness
construction, and identification of that valuation ring with `O` are still
work **inside** this leaf. Mathlib local-field instances give a DVR and
adic completeness for a ring of integers **after** the local-field
structure is supplied; they do not manufacture it for `FractionRing R`
[E6]. A Dedekind domain alone is not a local complete DVR.

### L1 — continuous lattice and reduction bridge, M after L0-N

```lean
def latticeGaloisRep (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ) :
    GaloisRep ℚ O Λ
theorem latticeGaloisRep_toRepresentation :
    (latticeGaloisRep ρK Λ hΛ).toRepresentation =
      StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable
theorem lattice_generic_equiv :
    ∃ e : (K ⊗[O] Λ) ≃ₗ[K] W,
      ((latticeGaloisRep ρK Λ hΛ).baseChange K).conj e = ρK
theorem lattice_residue_equiv :
    ∃ e : (ResidueField O ⊗[O] Λ) ≃ₗ[ResidueField O]
        StableLattice.Reduction O W Λ,
      ∀ g x, e (((latticeGaloisRep ρK Λ hΛ).baseChange (ResidueField O)) g x) =
        StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g (e x)
```

Dependencies: `normalization_padic_order`; `StableLattice.latticeRep`,
`.reducedRep`, `.latticeRep_apply_coe`, `.reducedRep_mk`, `.finrank_reduction`;
`Submodule.IsLattice.finite`, `.free`, `.rank'`;
`Module.Basis.extendOfIsLattice`; `TensorProduct.quotTensorEquivQuotSMul`;
`GaloisRep.baseChange`, `.conj`, `.toRepresentation` [E3, E5, E6].
Continuity is into `moduleTopology O (Module.End O Λ)`, which is the
actual `GaloisRep` definition, not an arbitrary subtype topology [E5].
Install `hΛ.isLattice` as a local instance when using the lattice API.
Prove finite/discrete residue coefficient instances and rank two.

For an arbitrary compact-group representation, an additional optional
contract is `IsOpen (StableLattice.latticeStabilizer ρK.toRepresentation Λ₀ : Set Γ)`.
Only after proving it may one invoke
`StableLattice.exists_isStableLattice_proof` [E3]. In this route the
normalized original model gives a starting stable lattice; constructing
that embedding avoids treating openness as a free consequence of the port.

### L2 — coefficient extension flatness, L

```lean
theorem flat_three_normalization (N : NormalizedOrderData R)
    (hflat : ρ.IsFlatAt v₃) : (ρ.baseChange N.O).IsFlatAt v₃
```

Dependencies: `normalization_padic_order`, `GaloisRep.IsFlatAt.cond`,
`GaloisModule.IsFiniteFlat.finPow`, `.quotient`, `.map` [E5]. For each
open `J : Ideal O`, choose `n` with `3^n (O/J)=0`, and a finite set of
`R`-module generators of `O/J`. Construct the equivariant surjection from
finitely many copies of `V/3^nV` to `(O/J) ⊗[R] V`; identify tensor and
quotient representations and their local actions. All open ideals, not
only the maximal ideal, are required. Do not invoke
`B5Inputs.flatAt_quotient` for the nonsurjective map `R → O` [E5].

### L3 — finite-flat subobjects, L

```lean
-- Same Dedekind/fraction-field/Galois/separably-closed setup as .quotient.
theorem GaloisModule.IsFiniteFlat.subobject
    (hX : GaloisModule.IsFiniteFlat A F Fbar X)
    (i : Y →+[Fbar ≃ₐ[F] Fbar] X) (hi : Function.Injective i) :
    GaloisModule.IsFiniteFlat A F Fbar Y
```

Proposed public name is exactly `GaloisModule.IsFiniteFlat.subobject`,
not in namespace `ThreeAdicPlan`. Dependencies:
`HopfAlgebra.IsFiniteFlat.quotient_comap`,
`Ideal.IsHopfIdeal.comap`,
`GaloisModule.GenericFiber.pullbackBialgHom`,
`GaloisModule.GenericFiber.pointsEquivariantAddEquiv` [E5]. Construct the
schematic closure of the generic subgroup; its coordinate ring is a
Hopf **quotient**, whereas a quotient of point modules involves a Hopf
subalgebra. Prove that this closure's generic points are precisely `Y`,
equivariantly. The existing `.quotient` is not the desired variance.
Account for finite/continuous action instances inherited through `i`.

### L4 — commensurate-lattice flatness, M after L1–L3

```lean
theorem flat_three_of_stable_lattice
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hflat : (latticeGaloisRep ρK Λ₀ h₀).IsFlatAt v₃) :
    (latticeGaloisRep ρK Λ hΛ).IsFlatAt v₃
```

Dependencies: `latticeGaloisRep`, `flat_three_normalization` for the
initial model; `Submodule.IsLattice.exists_smul_le`, `.smul_of_ne_zero`,
`StableLattice.Stabilizes.smul`; proposed
`GaloisModule.IsFiniteFlat.subobject`, existing `.quotient`, `.map` [E3, E5].
Scale to `ϖ^a Λ₀ ≤ Λ ≤ Λ₀`. For each `n`, realize `Λ/ϖ^nΛ` as a
quotient of the submodule `Λ/ϖ^(n+a)Λ₀` inside `Λ₀/ϖ^(n+a)Λ₀`.
Prove equivariance, local-action compatibility, and open-ideal cofinality.
The port's `reducedRep_smul_equiv` covers only maximal-ideal reduction;
finite higher levels and the continuous scaling identification still need
construction [E3].

### L5 — saturated quotient at 2, M after L1

```lean
-- TameTwo is exactly Defs.lean's isTameAtTwo proposition, not all of HR.
theorem tame_two_of_stable_lattice
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hπ : TameTwo (latticeGaloisRep ρK Λ₀ h₀)) :
    TameTwo (latticeGaloisRep ρK Λ hΛ)
```

Dependencies: `lattice_generic_equiv`, `latticeGaloisRep`,
`Submodule.IsLattice.exists_smul_mem` [E3], and principal fractional-ideal
and saturated-submodule algebra to develop in this leaf. Extend the
functional to `W →ₗ[K] K`; its image on `Λ` is a nonzero finitely generated
fractional ideal. Divide by a generator to obtain a surjection `Λ →ₗ[O] O`.
Retain the original local `GaloisRep ℚ_[2] O O` character, its inertia
kernel inclusion and square-one property, and prove continuity.
Do not replace this with a Frey-specific quotient construction.

### L6 — all-lattice HR, M after L0-N–L5

```lean
theorem hardlyRamified_of_stable_lattice (hρ : HR ρ)
    (N : NormalizedOrderData R)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ) :
    HR (latticeGaloisRep ρK Λ hΛ)
```

Dependencies: `normalization_padic_order`, `lattice_generic_equiv`,
`flat_three_normalization`, `flat_three_of_stable_lattice`,
`tame_two_of_stable_lattice`; `GaloisRepresentation.IsHardlyRamified.det`,
`.isUnramified`, `.isFlat`, `.isTameAtTwo`; `IsFractionRing.injective` [E2, E6].
Transport determinant and away-from-6 inertia identities through the
injective generic-fibre map. For reductions, first prove the proposed
`GaloisRepresentation.B5Inputs.hardlyRamified_of_surjective_coefficients`
(L6r, §5.1), then combine it with `lattice_residue_equiv`. The existing
`hardlyRamified_quotient` requires `[Module.Free ℤ_[p] A]` even for its
target. A nonzero residue field of characteristic p cannot have that
instance. Its proof is reusable, but its statement cannot be applied
directly to `A = ResidueField O` [E5]. Normalization HR and its
initial lattice embedding are part of this assembly, not assumed results.

### Q0 — initial characters and nontriviality, M

```lean
-- Q0a: algebra only, independently implementable; estimate M, not a promised S.
theorem isExtensionOf_det_one_of_trivial_quotient
    (ρ : Representation k G V) (hdim : Module.finrank k V = 2)
    (χ : G →* kˣ) (hdet : ∀ g, LinearMap.det (ρ g) = (χ g : k))
    (π : V →ₗ[k] k) (hs : Function.Surjective π)
    (hπ : ∀ g v, π (ρ g v) = π v) :
    StableLattice.IsExtensionOf ρ χ 1
-- Q0b: after reduction HR and R13, instantiate Q0a with χ̄₃.
theorem residual_characters (hρΛ : HR ρΛ) :
    StableLattice.IsExtensionOf ρbarΛ.toRepresentation χ̄₃ 1 ∧ χ̄₃ ≠ 1
```

Dependencies: proposed `isExtensionOf_det_one_of_trivial_quotient`,
`hardlyRamified_of_stable_lattice`, `lattice_residue_equiv`, R13;
proposed `GaloisRepresentation.B5Inputs.hardlyRamified_of_surjective_coefficients`
(L6r), `GaloisRepresentation.IsHardlyRamified.det`,
`StableLattice.exists_character_of_stable_line`,
`StableLattice.IsExtensionOf.congr` [E2, E3, E5]. Kernel of `π` has rank
one; choose an adapted basis and use determinant to identify its character.
Complex conjugation evaluates `χ̄₃` to `−1`; establishing this particular
Galois/coefficient comparison is included in Q0b, not supplied by the
involution dimension theorem. R0a supplies characteristic 3.
Then `Or.inr` gives `HasSemisimplification ρbarΛ 1 χ̄₃` with the port's
ordering, and independence transfers that hypothesis between lattices.
The all-lattice trivial quotients still require R13 on each lattice.

### Q1, Q2, Q3 — use the port, then bridge it

Q1 uses §5.5's ring/field/module setup and an additional local
`[ρ.IsIrreducible]` instance. Given `hdim`, `Λ₀`, `h₀`, and
`HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) φ₁ φ₂`, it returns
a stable lattice with `IsExtensionOf ... φ₁ φ₂` and
`¬ IsSplitExtensionOf ... φ₁ φ₂`; neither `hQ` nor `hne` is an input. Its endpoint is
`StableLattice.ribet_lemma_proof`; unlike the upstream admitted statements,
the port retains the `_proof` endpoints and omits the admitted unsuffixed
versions [E3]. Q2 needs no new proof; Q2-port is §5.2. Q3 is §5.5.
Do not omit `¬ StableLattice.IsSplitExtensionOf` from a replacement wrapper.

### C0 — integral rank-one characters, M (possibly L)

```lean
theorem integral_characters_of_reducible (hρΛ : HR ρΛ)
    (hred : ¬ ρK.IsIrreducible) :
    ∃ ψ₁ ψ₂ : Γ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Flat3 ψ₁ ∧ Flat3 ψ₂ ∧
      UnramifiedOutsideThree ψ₁ ∧ UnramifiedOutsideThree ψ₂ ∧
      GenericExtensionOf ρK ψ₁ ψ₂ ∧ ψ₁ * ψ₂ = χ₃
```

`Flat3 ψ` means all open-ideal reductions of the **rank-one** character
have local finite-flat models; it is not rank-two HR.
`GenericExtensionOf` means the port's `IsExtensionOf` after mapping units
to `K`, plus the specified integral lattices/maps. Dependencies: Q3,
`lattice_generic_equiv`, `GaloisModule.IsFiniteFlat.subobject`, `.quotient`,
`flat_three_of_stable_lattice`,
`StableLattice.exists_character_of_stable_line` [E3, E5]. Build the
saturated intersection with a stable generic line, prove its kernel and
quotient free of rank one over **O**, and make their characters continuous.
The HR quotient and determinant make inertia at 2 unipotent. Its rank-one
subquotients in characteristic zero are trivial on inertia. This
characteristic-zero calculation is distinct from R2's characteristic-3 cube.

### C1 — uniform pure finite levels, L after residual work

```lean
theorem rank_one_pure_levels (ψ : Γ →* Oˣ) (hc : Continuous ψ)
    (hf : Flat3 ψ) (hur : UnramifiedOutsideThree ψ) :
    (∀ n g, Ideal.Quotient.mk (𝔪^n) (ψ g : O) = 1) ∨
    (∀ n g, Ideal.Quotient.mk (𝔪^n) (ψ g : O) =
      Ideal.Quotient.mk (𝔪^n) (χ₃ g : O))
```

Dependencies on the chosen route: `global_model_away_two`,
`simple_D_three`, `D_three_sorted_filtration`,
`D_etale_three_constant`, `D_multiplicative_three_cyclotomic`,
`extend_coefficient_action` (R0b/R1/R9/R11/R12).
Prove that a rank-one residual coefficient representation has one pure
character, and every `ϖ`-power layer has that same type. The disjunction
must stay **outside** `∀ n`; neither a residual congruence nor
semisimplification independence gives the conclusion. Alternative:
`global_model_over_int` and a new Fontaine B classification over ℤ,
priced **XL**, not an available repo theorem [E8].

### C2 — exact characters and trace, S + M

C2a's exact conditional statement is §5.4. C2b remains:

```lean
theorem domain_trace (hρ : HR ρ) [IsDomain R] :
    ∀ g, LinearMap.trace R V (ρ g) =
      1 + algebraMap ℤ_[3] R
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv)
```

Dependencies: `integral_characters_of_reducible`, `rank_one_pure_levels`,
`ThreeAdicPlan.character_eq_one_or_of_power_quotients` (§5.4),
`GaloisRepresentation.B5Inputs.trace_eq_one_add_det_of_trivial_quotient`,
`.trace_baseChange_conj`, `.padic_domain_map_injective` [E4, E5].
Use exact determinant and complex conjugation to exclude equal choices
for `ψ₁,ψ₂`. If the trivial character is the subobject, use its quotient
character (or duality/triangular trace algebra); T1's functional hypothesis
cannot be assumed in that orientation. Descend along `R ↪ K` and evaluate
with `GaloisRepresentation.B5Inputs.cyclotomicCharacter_adicArithFrob`
[E7]. The all-ring `three_adic` statement needs additional work beyond
this domain contract; do not silently change its signature [E2].

## 4. Remaining residual contracts

All names in this section are **proposed `ThreeAdicPlan` declarations**
unless qualified as existing. `FF B` is finite flat commutative group-scheme
(or Hopf-algebra) model data over `B` with geometric points and generic
comparison maps; it is not a predicate containing a classification theorem.
`DModel W` adds an identification of points with `W`, 3-primary order and
square-zero inertia at 2. `K₀` is the splitting field of `X³−2` over ℚ.
`PointField` means the field cut out by the **full** point action.
`ShortExact...` includes actual maps and exactness. Here `χ₃` is the
ℤ₃-valued cyclotomic character acting on finite 3-primary point groups;
coefficient images are taken only when a coefficient action is specified. These records are
missing interface work owned by R1/R4/R10, not existing Lean APIs [E5, E7, E8].
Statements using `ℤ[1/2]`, relative ramification, `Pure`, or these records
are schematic, with the mathematical meanings specified here.

### R0 — characteristic and coefficient action: S + M

R0a is pasteable in §5.3. R0b's contract, **M after R1**:

```lean
theorem extend_coefficient_action (M : ModelOverZInvTwo W)
    (a : k →+* Module.End (ZMod 3) W)
    (ha : ∀ t g w, a t (g • w) = g • a t w) :
    ∃ aM : k →+* End M, ∀ t, genericEnd (aM t) = a t
```

Dependencies: `charP_three_of_finite_padic_algebra`;
`global_model_away_two`, `raynaud_extend_generic_morphism` (R1).
Extend the field action through uniqueness of morphisms and verify ring
laws; a list of individually lifted endomorphisms does not suffice.

### R1 — global models and morphisms, L

```lean
theorem global_model_away_two (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {2, 3} W) : Nonempty (ModelOverZInvTwo W)
theorem global_model_over_int (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {3} W) : Nonempty (ModelOverInt W)
theorem raynaud_extend_generic_morphism
    (X Y : FF ℤ_[3]) (hkX : KilledByPowerOf 3 X) (hkY : KilledByPowerOf 3 Y)
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f
```

Dependencies: existing `GaloisModule.IsFiniteFlat`,
`GaloisModule.GenericFiber.hopfAlgebra`, `.pointsEquivariantAddEquiv`
[E5]; the displayed Raynaud statement is a **new** substantial part of
this leaf, using base ramification `e(ℚ₃)=1<3−1`. Glue finite étale data
away from 3 with the local model, including generic comparisons and
morphism compatibility. Do not make global gluing depend on R0b: first
construct models/morphism extension, then lift the coefficient action.

### R3 — tame ramification at 2, L

```lean
theorem inertia_two_sq_zero (hρ : HR ρbar) :
    ∀ σ ∈ inertiaTwo, (ρbar.localAtTwo σ - 1)^2 = 0
theorem ramification_two_dvd_three
    (hD : DModel W) (hkill : ∀ w : W, (3 : ℕ) • w = 0) :
    e_two (PointField W / ℚ) ∣ 3
```

Dependencies: `GaloisRepresentation.IsHardlyRamified.det`, `.isTameAtTwo`,
`GaloisRepresentation.cube_eq_one_of_sub_one_sq_eq_zero` [E2, E4]; R0a;
local wild/tame inertia and point-field/completion comparisons to prove
in this leaf. The wild pro-2 image in a 3-group is trivial; the tame image
is **cyclic**, and R2 bounds its exponent. Omitting cyclicity would leave
an invalid order bound when the coefficient field exceeds `𝔽₃`.

### R4 — Kummer object and augmented field, L

```lean
theorem exists_kummer_two_model :
    ∃ G₂ : FF (ℤ[1/2]), KilledBy 3 G₂ ∧ InCategoryD G₂ ∧
      Nonempty (PointField G₂ ≃ₐ[ℚ] K₀)
theorem simple_D_killed_three (H : FF (ℤ[1/2]))
    (hs : Simple H) (hD : InCategoryD H) : KilledBy 3 H
theorem augmented_field_data (H : FF (ℤ[1/2]))
    (hs : Simple H) (hD : InCategoryD H) :
    ∃ L, IsPointField (H.prod G₂) L ∧ Nonempty (K₀ →ₐ[ℚ] L) ∧
      IsGalois ℚ L ∧ NumberField.IsTotallyComplex L ∧
      UnramifiedOutside {2,3} (L / ℚ) ∧ e_two (L / ℚ) ∣ 3
```

Dependencies: `global_model_away_two`, `ramification_two_dvd_three`,
`GaloisModule.IsFiniteFlat.prod`,
`GaloisRepresentation.Chebotarev.exists_finiteGalois_realization` [E5, E7].
Construct `G₂` and its point field, not merely a finite quotient with the
right name. R4's simple-killed-by-3 result is needed before R5 uses the
`n=1` Fontaine estimate. R6 proves the field's degree and ramification.

### R5 — discriminant upper bound, XL

```lean
theorem fontaine_different_bound_killed_three
    (M : FF ℤ_[3]) (hk : KilledBy 3 M) :
    normalizedDifferentExponent (LocalPointField M / ℚ_[3]) < (3/2 : ℚ)
theorem augmented_discriminant_bound
    (hL : IsPointField (H.prod G₂) L) (hs : Simple H) (hD : InCategoryD H) :
    |(NumberField.discr L : ℝ)| ≤
      ((2 : ℝ)^(2/3 : ℝ) * (3 : ℝ)^(3/2 : ℝ)) ^ Module.finrank ℚ L
```

Dependencies: `fontaine_different_bound_killed_three` (new in this leaf),
`simple_D_killed_three`, `augmented_field_data`,
`ramification_two_dvd_three`; develop different/discriminant comparison.
The existing `Odlyzko.not_discriminant_le_fontaine_bound` consumes this
bound; it does not prove it [E7]. Include ramification at 2 for the
augmented field. A bound on the original representation's kernel field
is insufficient for R8's divisibility-by-six argument.

### R6 — explicit sextic field, L

```lean
theorem kummer_two_field_data :
    Module.finrank ℚ K₀ = 6 ∧ NumberField.classNumber K₀ = 1 ∧
    UniquePrimeAboveThree K₀ ∧ ResidueFieldAtThreeIsF3 K₀ ∧
    ResidueUnitsGeneratedByNegOne K₀ ∧ e_two (K₀ / ℚ) = 3
```

Dependencies: the definition of `K₀` from R4; explicit integral-basis,
class-number and prime-decomposition calculations are work within R6.
`NumberField.classNumber` is the target invariant, not an existing
certificate for this sextic field [E7, E8]. `UniquePrimeAboveThree` includes
a specified prime, and the residue/unit assertions concern that prime.
The quadratic cyclotomic field's class number would not suffice.

### R7 — no quadratic extension of K₀, L / XL dependency

```lean
theorem no_quadratic_extension_auxiliary
    [NumberField L] [Algebra K₀ L] [FiniteDimensional K₀ L]
    (hur : UnramifiedOutside {primesAboveThree} (L / K₀)) :
    Module.finrank K₀ L ≠ 2
```

Dependencies: `kummer_two_field_data`; new specialized ray-class/reciprocity
argument or a complete Kummer square-class calculation. For the former,
prove the quadratic conductor divides the unique prime above 3 and show
its ray class group has no quotient of order 2, using class number 1 and
the residue image of `−1`. This arithmetic is not provided by the Ribet
port or the numerical bound [E3, E7, E8]. The conductor/reciprocity work is
inside this leaf's XL risk; it is not an unpriced theorem assumption.

### R9 — simple finite-flat objects, L after R4–R8

```lean
theorem simple_D_three (H : FF (ℤ[1/2])) (hs : Simple H)
    (hD : InCategoryD H) :
    Nonempty (H ≅ constantThree) ∨ Nonempty (H ≅ muThree)
```

Dependencies: `augmented_field_data`, `augmented_discriminant_bound`,
`kummer_two_field_data`, `no_quadratic_extension_auxiliary`, root
`auxiliary_degree_eq_six_or_twelve` [E4], and
`raynaud_extend_generic_morphism` for model uniqueness.
Derive degree divisibility using the actual `K₀` inclusion. R8 leaves
6 or 12; R7 excludes 12 after proving `L/K₀` unramified outside 3.
Then use `Gal(K₀/ℚ) ≅ S₃` and the normal 3-subgroup's trivial action on
simple characteristic-3 modules. Identify **models**, not just generic
representations. Restrict to `𝔽₃` and take actual simple factors; do not
assume a k-simple representation stays simple after forgetting scalars.

### R10 — reverse finite-flat Ext vanishing, XL

```lean
theorem split_extension_mu_three_by_constant_three
    (E : ShortExactFiniteFlatSequence (ℤ[1/2]) constantThree muThree) :
    Nonempty E.Splitting
```

Sequence orientation: `0 → constantThree → E.middle → muThree → 0`.
Dependencies: `global_model_away_two`, `raynaud_extend_generic_morphism`;
local connected–étale splitting, global/local Kummer classes and explicit
unit/class computations in `ℚ(ζ₃)` and `ℚ₃(ζ₃)` are new work here.
The final mod-9 criterion is not the full Ext proof. The admitted Mazur
scaffold is not a substitute [E7]. This is independent of Q2, which
**assumes an invariant quotient** and proves a linear splitting.

### R11 — pure actions at finite levels, L

```lean
theorem D_etale_three_constant (H : FF (ℤ[1/2]))
    (hD : InCategoryD H) (hf : HasFiltration H constantThree) :
    Pure H.geometricPoints 1
theorem D_multiplicative_three_cyclotomic (H : FF (ℤ[1/2]))
    (hD : InCategoryD H) (hf : HasFiltration H muThree) :
    Pure H.geometricPoints χ₃
```

Dependencies: `global_model_away_two`,
`NumberField.InertiaComparison.intermediateField_eq_bot_of_localInertia`
[E7]; finite 3-group abelian quotients, tame Frobenius relation at 2 and
Cartier duality to supply in this leaf. `Pure` is **pointwise scalar action**,
not just a list of composition factors. Trivial factors alone allow
nontrivial unipotent extensions; the unramified arithmetic kills them.

### R12 — coefficient-functorial sorted filtration, L

```lean
theorem D_three_sorted_filtration (H : FF (ℤ[1/2])) (hD : InCategoryD H) :
    ∃ E : ShortExactFiniteFlatSequenceWithMiddle H,
      HasFiltration E.left muThree ∧ HasFiltration E.right constantThree ∧
      PreservedByAllEndomorphisms E
```

Dependencies: `simple_D_three`, `split_extension_mu_three_by_constant_three`,
proposed `GaloisModule.IsFiniteFlat.subobject` with global model analogues,
existing `.quotient` [E5]. Construct finite-flat composition series and
sort by swapping split adjacent factors. Prove functoriality using Hom
vanishing of distinct generic characters. R11 subsequently identifies the
actions; R12 need not assume R13 (which would create a cycle).

### R13 — k-linear quotient and mod_three, M after arithmetic

```lean
theorem trivial_quotient_over_coefficients
    (hρ : HR ρbar) (hmodel : DModel (ρbar.restrictScalars (ZMod 3)))
    (hsorted : SortedFiltrationWithPureActions hmodel) :
    ∃ π : V →ₗ[k] k, Function.Surjective π ∧ ∀ g v, π (ρbar g v) = π v
```

Dependencies: `charP_three_of_finite_padic_algebra`,
`extend_coefficient_action`, `global_model_away_two`,
`D_three_sorted_filtration`, `D_etale_three_constant`,
`D_multiplicative_three_cyclotomic`,
`GaloisRepresentation.IsHardlyRamified.det` [E2].
`SortedFiltrationWithPureActions` combines R12's maps with R11's pointwise
action conclusions; it must not assert the desired k-linear functional.
Use the coefficient-stable quotient, or the nondegenerate trace pairing
`Algebra.traceForm_nondegenerate` [E7]. Determinant at complex conjugation
excludes an entirely cyclotomic rank-two action. Obtain a nonzero k-linear
invariant functional, hence a surjective one. Do not identify `k` with
`ZMod 3` or divide by `[k:𝔽₃]`. Discharging these inputs, including R3 to
place the model in D, is what finally removes `mod_three`'s admission.

## 5. Capped dispatch: exact signatures

These are proposed signatures using existing vocabulary, **not elaboration
claims**. Paste a signature into the indicated imports/namespace and add
its proof. Future acceptance: targeted build and `#print axioms` for the
new declaration, with no admission imported through `mod_three` or
`three_adic`. Those checks were deliberately not run in this docs-only task.

Ready **now**: 1, 2, 3, 4, each with only source-present dependencies
[E3–E5, E7]. Dispatch 5 after 2 lands. Do not redispatch R2/R8/Q2/C3/T1/A0 or
the involution theorem. The first leaf repairs the HR signature needed
for residue coefficients;
the second connects the newly ported nonsplitting predicate to the existing
quotient argument. The four ready leaves are independent of one another.

### 5.1 L6r: HR transport to residue coefficient rings

**S, cap 2 h; ready now.** Proposed file
`FLT/GaloisRepresentation/HardlyRamified/CoefficientQuotient.lean`.
Import `FLT.GaloisRepresentation.HardlyRamified.B5Inputs`.

```lean
open scoped TensorProduct

namespace GaloisRepresentation.B5Inputs

theorem hardlyRamified_of_surjective_coefficients
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R A : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra ℤ_[p] A] [Algebra R A] [IsScalarTower ℤ_[p] R A]
    [ContinuousSMul R A] (hsurj : Function.Surjective (algebraMap R A))
    {V : Type} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (hVA : Module.rank A (A ⊗[R] V) = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ) :
    IsHardlyRamified hpodd hVA (ρ.baseChange A)

end GaloisRepresentation.B5Inputs
```

Dependencies: `GaloisRepresentation.B5Inputs.flatAt_quotient`,
`GaloisRep.baseChange`, `.conj`, `.ker_conj`, `.ker_baseChange`,
`LinearMap.det_baseChange`, `LinearMap.baseChange_surjective`,
`AlgebraTensorModule.rid` [E5]. Reuse the four-clause proof of
`GaloisRepresentation.B5Inputs.hardlyRamified_quotient`; do not invoke
that theorem, since its extra target hypotheses are precisely the problem.
All coefficient finite/free/module-topology hypotheses have been removed;
the representation module remains finite free, and coefficient continuity,
algebra compatibility and rank are explicit. Verify no body step needs
the removed assumptions. Alternatively generalize the original declaration
in place with this signature and keep its original name, which avoids a
second proof; update downstream imports accordingly. The application to
`ResidueField O` still needs L1's topology, continuous scalar action,
surjectivity and rank instances. This leaf alone does not transport HR
between distinct integral lattices.

### 5.2 Q2-port: trivial quotient splits the port's opposite extension

**S, cap 2 h; ready now.** Proposed file
`FLT/GaloisRepresentation/HardlyRamified/RibetAdapters.lean`.
Imports `FLT.KnownIn1980s.Ribet_Lemma.Proofs` and
`FLT.GaloisRepresentation.HardlyRamified.ThreeAdicAlgebra`.

```lean
namespace StableLattice

theorem isSplitExtensionOf_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (hext : IsExtensionOf ρ 1 χ)
    (hne : ∃ g, χ g ≠ 1)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    IsSplitExtensionOf ρ 1 χ

end StableLattice
```

Proof plan: unpack the port's line `L`; show `π|L` is nonzero. Otherwise
apply `π` to `ρ g v − χ(g) • v ∈ L`, choosing `χ(g) ≠ 1` and `π(v)=1`.
Since `L` has rank one, choose `l ∈ L` with `π(l)=1`; decompose every
`v` as `π(v) • l + (v − π(v) • l)`. This gives
`IsCompl L (LinearMap.ker π)`. Invariance makes the kernel stable; the
extension's difference lies in both `L` and `ker π`, so it vanishes and
the kernel action is **χ**, as the port requires. Alternatively construct
the exact `i,q` maps and use
`GaloisRepresentation.stable_complement_of_trivial_quotient` [E4].
The direct proof avoids an unnecessary quotient-basis adapter. It does
not redo the arithmetic classification or claim χ is nontrivial without
an explicit hypothesis.

### 5.3 R0a: recover characteristic three

**S, cap 2 h; ready now.** Proposed file
`FLT/GaloisRepresentation/HardlyRamified/ResidualCharacteristic.lean`.
Import `Mathlib.NumberTheory.Padics.RingHoms` and
`Mathlib.RingTheory.DedekindDomain.Basic` (or `Mathlib` during development).

```lean
namespace ThreeAdicPlan

theorem charP_three_of_finite_padic_algebra
    (k : Type*) [Field k] [Finite k] [Algebra ℤ_[3] k] :
    CharP k 3

end ThreeAdicPlan
```

Dependencies: `RingHom.ker_isPrime`, `RingHom.injective_iff_ker_eq_bot`,
`Ideal.IsPrime.isMaximal`, `IsLocalRing.eq_maximalIdeal`,
`PadicInt.ker_toZMod`, `CharP.charP_iff_prime_eq_zero` [E7].
The kernel of `algebraMap ℤ_[3] k` is nonzero: an injection would make the
characteristic-zero domain `ℤ_[3]` finite. It is a nonzero prime of a DVR,
hence the unique maximal ideal. `PadicInt.ker_toZMod` puts 3 in that
ideal, so `(3 : k)=0`. Use the prime characteristic criterion. This leaf
adds no field-equality assumption and no coefficient-model action claim.
R0b remains separate.

### 5.4 C2a: exact character from a uniform choice at all levels

**S, cap 1 h; ready now, lower priority.** Proposed file
`FLT/GaloisRepresentation/HardlyRamified/CharacterSeparation.lean`.
Import `FLT.Mathlib.RingTheory.AdicCompletion.PowerQuotients`.

```lean
namespace ThreeAdicPlan

theorem character_eq_one_or_of_power_quotients
    {G O : Type*} [Group G] [CommRing O]
    (I : Ideal O) [IsHausdorff I O] (ψ χ : G →* Oˣ)
    (hlevels :
      (∀ (n : ℕ) (g : G), Ideal.Quotient.mk (I ^ n) (ψ g : O) = 1) ∨
      (∀ (n : ℕ) (g : G), Ideal.Quotient.mk (I ^ n) (ψ g : O) =
        Ideal.Quotient.mk (I ^ n) (χ g : O))) :
    ψ = 1 ∨ ψ = χ

end ThreeAdicPlan
```

Dependencies: root `eq_of_all_power_quotients` [E4], unit and monoid-hom
extensionality. Apply C3 pointwise in the selected branch, then extensionality.
This is a short consumer of C3, not another proof of separatedness. Its
only role is a clean C1/C2 interface; it proves none of C1's congruences.

### 5.5 Q3: algebraic all-lattice contradiction

**S, cap 2 h after 5.2; not ready independently today.** Add to
`RibetAdapters.lean` with the same imports and §5.2 available.

```lean
namespace StableLattice

open IsLocalRing

theorem not_isIrreducible_of_all_lattices_trivial_quotient
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {W : Type*} [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] [FiniteDimensional K W]
    {G : Type*} [Group G]
    [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G W) (hdim : Module.finrank K W = 2)
    (Λ₀ : Submodule O W) (h₀ : IsStableLattice ρ Λ₀)
    (χ : G →* (ResidueField O)ˣ) (hne : ∃ g, χ g ≠ 1)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) 1 χ)
    (hQ : ∀ (Λ : Submodule O W) (h : IsStableLattice ρ Λ),
      ∃ π : Reduction O W Λ →ₗ[ResidueField O] ResidueField O,
        Function.Surjective π ∧
          ∀ g v, π (reducedRep ρ Λ h.stable g v) = π v) :
    ¬ ρ.IsIrreducible

end StableLattice
```

Dependencies: `StableLattice.ribet_lemma_proof` [E3] and proposed
`StableLattice.isSplitExtensionOf_of_trivial_quotient` (§5.2).
Install the hypothetical irreducibility proof as an instance, invoke
Ribet with characters `1,χ`, apply `hQ` to its witness lattice, and
contradict its nonsplitting conclusion using §5.2. No topology or HR is
needed by this conditional statement. Arithmetic discharge of `hss`,
`hne`, and especially **every-lattice** `hQ` remains L6/L6r/R13/Q0.

## 6. Review and acceptance boundaries

The following are intentional limits, not hidden assumptions:

- A body in the port is not a fresh transitive axiom audit. The literal
  admission-token search finds comment mentions only in the five port
  files; the dependency entry `stable_lattices.lean` imports `Mathlib`
  [E3]. Implementers must check the actual endpoints they use.
- The port assumes an abstract complete DVR and fraction field; it does
  not normalize the original coefficient order. Algebraic reduction need
  not yet be the continuous coefficient-base-change representation [E3, E5].
- Residual classification, preserving flatness for all lattices, and pure
  higher levels are distinct obligations. None follows from changing the
  residual extension order. R10 is geometric Ext vanishing; Q2 is
  conditional representation-theoretic splitting.
- There is no cycle through `mod_three`: all small adapters and Q3 must
  compile with it absent from their proof dependencies. Full R13 removes
  that admission only after its arithmetic inputs are proved [E2].
- A domain theorem is a valid intermediate target, but does not close the
  all-ring `three_adic`. Any narrowing of the public theorem or change to
  the consumer is a separate integration change [E2].

Plan review passes: (1) reconciled all original leaf labels, including the
L0 collision; (2) compared exact port predicates and character orientation;
(3) checked the dependency graph for arithmetic hidden in conditionals and
for possible R0b/R1 and R13/Q0 cycles; (4) caught the ℤₚ-free target
restriction in HR quotient transport, added L6r, and checked proposed
S signatures for missing vocabulary and separated source checks from elaboration claims.
These are source/design reviews, not substitute builds.

## 7. Reproducible evidence ledger

Run from the worktree root. These commands were run during this audit;
combined commands below group the same inspected sources. `rg` exit 1
on E8 means no matching declaration names in that search scope.
All existing-declaration claims above refer to these source checks.
Local `origin/main` is the pinned comparison ref, **not a fresh remote
status claim**. Historical mathematical citations and the earlier chain
come from the read-only audit [E0]; this task does not re-download sources.

**E0 — task and original inventory.**

```bash
cat BRIEF.md
cat AUDIT.ref.md
```

Evidence: docs-only/no-build/commit scope; original R0–R13, L0–L6,
Q0–Q3, C0–C3 contracts and historical source argument. These supplied
reference inputs are not included in this documentation commit; the plan
above carries their relevant contracts so implementers need not have them.

**E1 — snapshot and unchanged inputs.**

```bash
git rev-parse HEAD
git rev-parse origin/main
git -C .lake/packages/mathlib rev-parse HEAD
date -u '+%Y-%m-%dT%H:%M:%SZ'
git status --short
git log --oneline -12 origin/main
```

Evidence: revisions at the top; initial untracked `AUDIT.ref.md`; main's
R8/C3, R2/Q2, A0 and involution commits. No remote fetch asserted.

**E2 — actual target, HR definition, domain consumer.**

```bash
cat FLT/GaloisRepresentation/HardlyRamified/{Threeadic,ModThree,Defs}.lean
rg -n 'three_adic|IsDomain' FLT/GaloisRepresentation/HardlyRamified/{Family,PrimeField}.lean
```

Evidence: both target admissions, exact invariant-functional orientation,
all-ring three-adic signature, four HR clauses, domain family model.

**E3 — port endpoints and their dependencies.**

```bash
cat FLT/KnownIn1980s/Ribet_Lemma/{Defs,Proofs}.lean
sed -n '85,435p' FLT/Slop/Ribet_Lemma/stable_lattices.lean
sed -n '85,280p' FLT/Slop/Ribet_Lemma/Brauer_Nesbitt.lean
sed -n '472,510p' FLT/Slop/Ribet_Lemma/Ribet_Lemma.lean
rg -n 'theorem|namespace|public import' FLT/Slop/Ribet_Lemma/*.lean
rg -n '\b(sorry|admit|axiom)\b' FLT/KnownIn1980s/Ribet_Lemma FLT/Slop/Ribet_Lemma
```

Evidence: exact `_proof` signatures, complete-DVR assumption and
irreducibility typeclass; sub/quotient ordering and split-complement
character; algebraic lattice/rank/scaling API; open-stabilizer requirement;
admission-token hits are comment prose, not proof bodies. No assertion
about unsuffixed public proof endpoints absent from this port.

**E4 — supplied main algebra leaves.**

```bash
cat FLT/GaloisRepresentation/HardlyRamified/{ThreeAdicAlgebra,ThreeAdicDegree,TraceLeaves,AbsIrredAdapter}.lean
cat FLT/Mathlib/RingTheory/AdicCompletion/PowerQuotients.lean
cat FLT/Mathlib/LinearAlgebra/InvolutionFixedSpace.lean
```

Evidence: precise names, namespaces, hypotheses, conclusions and proof
bodies for R2/R8/Q2/C3/T1/A0/involution. See E10 for source equality to main.

**E5 — continuous representations and finite-flat API.**

```bash
sed -n '30,115p' FLT/Deformations/RepresentationTheory/GaloisRep.lean
sed -n '375,430p' FLT/Deformations/RepresentationTheory/GaloisRep.lean
rg -n 'GaloisRep.baseChange|ker_baseChange|ker_conj' FLT/Deformations/RepresentationTheory/GaloisRep.lean
cat FLT/Deformations/RepresentationTheory/Flat.lean
cat FLT/GaloisRepresentation/HardlyRamified/B5Inputs.lean
rg -n 'IsFiniteFlat|pullbackBialgHom|pointsEquivariantAddEquiv|IsHopfIdeal.comap|namespace' FLT/GroupScheme/FiniteFlat.lean
sed -n '2372,2415p' FLT/GroupScheme/FiniteFlat.lean
```

Evidence: module topology in `GaloisRep`; all-open-ideal flatness;
surjectivity requirement for coefficient quotient transport; extra
ℤₚ-freeness hypotheses on both coefficients of `hardlyRamified_quotient`,
absent from `flatAt_quotient`;
trace/embedding lemmas; finite-flat product/power/quotient and Hopf closure
primitives, with the quotient theorem's actual direction and hypotheses.

**E6 — normalization and lattice foundations.**

```bash
cat .lake/packages/mathlib/Mathlib/Algebra/Module/Lattice.lean
rg -n 'theorem|lemma|instance' .lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean
rg -n 'theorem|lemma|instance' .lake/packages/mathlib/Mathlib/NumberTheory/LocalField/Basic.lean
cat .lake/packages/mathlib/Mathlib/NumberTheory/Padics/LocalField.lean
rg -n 'IsFractionRing.injective' .lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean
```

Evidence: lattice finite/free/rank/basis API; integral-closure results;
local-field ring-of-integers DVR, finite residue and complete/adic instances,
conditional on having the local-field structure.

**E7 — residual and final-trace foundations.**

```bash
rg -n 'not_discriminant_le_fontaine_bound|namespace' FLT/Odlyzko.lean
cat FLT/GaloisRepresentation/HardlyRamified/Chebotarev/FiniteGaloisRealization.lean
rg -n 'cyclotomicCharacter_adicArithFrob|namespace' FLT/GaloisRepresentation/HardlyRamified/Chebotarev/FrobeniusTraces.lean
cat FLT/FreyCurve/Serre/UnramifiedCharacter.lean
rg -n 'def |theorem|sorry|namespace' FLT/MazurChapter/AdmissibleGroupSchemes.lean
rg -n 'traceForm_nondegenerate|namespace' .lake/packages/mathlib/Mathlib/RingTheory/Trace/Basic.lean
cat .lake/packages/mathlib/Mathlib/FieldTheory/Finite/Trace.lean
rg -n 'ker_toZMod|residueField' .lake/packages/mathlib/Mathlib/NumberTheory/Padics/RingHoms.lean
rg -n 'injective_iff_ker_eq_bot|ker_isPrime' .lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean
rg -n 'Ideal.IsPrime.isMaximal' .lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Basic.lean
rg -n 'eq_maximalIdeal' .lake/packages/mathlib/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean
rg -n 'charP_iff_prime_eq_zero' .lake/packages/mathlib/Mathlib/Algebra/CharP/Basic.lean
rg -n 'classNumber' .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/ClassNumber.lean
```

Evidence: numerical lower bound, finite quotient realization, exact
Frobenius evaluation, Minkowski ingredient, admitted Mazur objects,
trace-pairing and R0a algebra APIs. No sextic-field certificate asserted.

**E8 — scoped missing-name search.**

```bash
rg -n 'normalization_padic_order|global_model_away_two|global_model_over_int|charP_three_of_finite_padic_algebra|extend_coefficient_action|raynaud_extend_generic_morphism|inertia_two_sq_zero|ramification_two_dvd_three|exists_kummer_two_model|augmented_field_data|kummer_two_field_data|augmented_discriminant_bound|no_quadratic_extension_auxiliary|simple_D_three|split_extension_mu_three_by_constant_three|D_etale_three_constant|D_multiplicative_three_cyclotomic|D_three_sorted_filtration|trivial_quotient_over_coefficients|flat_three_normalization|IsFiniteFlat\.(subobject|subgroup)|flat_three_of_stable_lattice|tame_two_of_stable_lattice|hardlyRamified_of_stable_lattice|residual_characters|not_isIrreducible_of_all_lattices_trivial_quotient|integral_characters_of_reducible|rank_one_pure_levels|rank_one_eq_one_or_cyclotomic|domain_trace|latticeGaloisRep|lattice_generic_equiv|hardlyRamified_of_surjective_coefficients|isSplitExtensionOf_of_trivial_quotient|character_eq_one_or_of_power_quotients' FLT .lake/packages/mathlib/Mathlib --glob '*.lean'
```

Evidence: no matches at this snapshot. Supplemented by the actual API
reads E2–E7; the absence claim is restricted to the searched names.

**E9 — inspect proposed-declaration dependencies and diff.**

```bash
git diff --check
rg -n '^### |^\| (R[0-9]+|L[0-9]|Q[0-9]|C[0-9]|T1|A0|Involution)' docs/THREE_ADIC_LATTICE_PLAN.md
```

Evidence: leaf coverage and formatting; not a Lean elaboration check.

**E10 — compare the already-supplied files with local main.**

```bash
git diff origin/main HEAD -- FLT/GaloisRepresentation/HardlyRamified/ThreeAdicAlgebra.lean FLT/GaloisRepresentation/HardlyRamified/ThreeAdicDegree.lean FLT/GaloisRepresentation/HardlyRamified/TraceLeaves.lean FLT/GaloisRepresentation/HardlyRamified/AbsIrredAdapter.lean FLT/Mathlib/RingTheory/AdicCompletion/PowerQuotients.lean FLT/Mathlib/LinearAlgebra/InvolutionFixedSpace.lean
```

Evidence: empty diff; these six source files equal the local main snapshot.
