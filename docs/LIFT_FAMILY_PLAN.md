# LF0: lifting and trace companions for the FLT spine

Source baseline: `6b0261b42f006644b966243ac348d2e726ac020c` (`task/lf0`).
Checked 2026-09-28 UTC by reading the callers, searching the source trees,
and inspecting the blueprint chapters named below. This is an implementation
plan, not a proof of lifting or the existence of compatible families.
Line references refer to that baseline unless explicitly marked new.

## Decision and scale

Keep the current assembly while developing a **Frey-only lifting input and
a p/3 trace companion** in parallel files. The final proof needs primes
**p ≥ 17**, not every odd prime, every finite residue field, or all members
of a compatible family. Preserve the existing general statements as separate
goals; a proof of the restricted inputs will require a small assembly rewrite.
Do not replace their bodies with another assumption and call that completion.

Follow the blueprint's potential-modularity/deformation route. In particular,
neither unrestricted deformation representability nor the abstract patching
theorem currently constructs the required arithmetic lift. Compatible
families require automorphic attachment and descent as well as patching.

**This is years-scale work.** A preliminary allowance for the remaining
shared route is **120,000–275,000 new Lean lines and 14,000–35,000 worker-hours**
(roughly 7–18 full-time worker-years at 2,000 hours/year). These are judgment
ranges for proof development, interface changes, review, and integration,
not measured productivity or a guaranteed upper bound. Several specialists
working for multiple years is a credible planning unit. Removing two names
from a dependency report does not measure the size of their mathematics.
The estimate excludes the separately planned Mazur theorem and already
implemented three-adic sorting. Shared prerequisites are counted once.

The first three bounded leaves below improve the interfaces and verification;
they do not prove any of the missing global existence theorems. L1 is supplied
with this delivery, in a new Mathlib-only module.

## What the current proof actually consumes

There are two callers, and they must not be confused:

* `FLT/GaloisRepresentation/HardlyRamified/PrimeField.lean:42` proves the
  generic `not_isIrreducible_of_prime_field` for `ZMod p`, `5 ≤ p`.
  Lines 53 and 61 invoke `lifts` and `mem_isCompatible` directly. Its legacy
  three-adic call is at line 72.
* `FLT/Assembly/PrimeField.lean:35` proves `not_isIrreducible_of_inputs`
  using explicit premises. Lines 48 and 56 consume lifting and families;
  line 67 uses the supplied `ThreeAdicFrobeniusTrace`, not that legacy call.
  This is the route used by the final positive-natural theorem.

The live assembly source chain is:

```text
Lift.lifts / Family.mem_isCompatible
  -> Assembly/ExistingInputs.lean:31,36
  -> FermatsLastTheorem.lean:23,27-29 supplies the two premises
  -> Assembly/ThreeInputFinal.lean:24
  -> Assembly/PrimePowerFinal.lean:39 (sorting supplies the 3-adic trace)
  -> Assembly/Proof.lean:45,27 (B4_of_inputs)
  -> Assembly/PrimeField.lean:35
  -> B5Inputs: quotient, compatibility, trace descent, Chebotarev criterion
  -> B4 reducibility + Mazur exclusion -> B3 -> B2 -> FLT
```

`FLT/Proof.lean:57` defines B4 only for `P : FreyPackage` with `17 ≤ P.p`.
`Assembly/Proof.lean:30` discards this bound and uses `P.hp5`; keeping it
permits the restricted input. `Proof.lean:81` and `:84` already handle the
small exponents and the reduction from Frey packages. A restriction to
p ≥ 17 still means infinitely many primes.

| Current quantifier or output | Actual use |
|---|---|
| `Lift.lean:25`: arbitrary finite field `k` | Only `ZMod p` with its canonical p-adic residue map |
| `Lift.lean:28`: arbitrary odd p | Generic B5 uses p ≥ 5; final B4 only p ≥ 17 |
| Arbitrary rank-two residual representation | Only `P.freyCurve.galoisRep P.p P.hppos` in B4 |
| Arbitrary universes | Assembly/Inputs uses `Type`; no universe-polymorphic existence is required |
| General finite free local lift ring R | Immediately replaced by a domain quotient A |
| Exact residual conjugacy | Used only to descend Frobenius traces in the final step |
| Family at every prime and every embedding | One p-adic embedding and one 3-adic embedding |
| Characteristic polynomials over a number field | Only their coefficient `-coeff 1`, the rank-two trace |
| Hardly ramified models at every odd prime | Only one integral domain model at 3 |
| Compatibility outside finite S | Needed only for prime q ≥ 5, q ≠ p; q ≠ 3 is automatic |

The determinant is supplied independently by
`FreyCurve.torsion_isHardlyRamified`,
`FLT/GaloisRepresentation/HardlyRamified/Frey.lean:95` and
`Defs.lean:108`. The endgame does not need family determinants, purity,
equality of representations across characteristics, or traces at bad primes.

### Weakest consumed consequence: residual Frobenius traces

Here is a complete proposed proposition, with an irreducibility premise
because the construction is used inside a contradiction. The helper is
independent of any lifting or family input. The block is a **statement
sketch**, not a declaration added to the library or a certified proof.
Use imports `FLT.Assembly.Proof` and `Mathlib.Topology.Instances.ZMod`.

```lean
open GaloisRepresentation
open scoped NumberField

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
```

This is the weakest *consumed trace consequence*, not a claim of a unique
logically weakest theorem: B4 itself, or nonexistence of Frey packages,
would also suffice. `FreyResidualTraceInput` merges both missing inputs
and the proved three-adic step. It does not separate their mathematics.
The exact adapter is a short application of
`B5Inputs.not_isIrreducible_of_frobenius_traces`
(`HardlyRamified/Chebotarev/FrobeniusTraces.lean:262`), using the determinant
and rank of Frey torsion, then the existing conditional Mazur assembly.

### Restricted lifting contract

For a separable implementation boundary, retain a genuine lift. The following
specialization is enough for generic B5; replace its universal residual
arguments with the Frey arguments above, and `5 ≤ p` with `17 ≤ P.p`,
for the strictly smaller final-assembly contract. This sketch uses the same
module and topological conventions as `Assembly/Inputs.lean:29`.

```lean
open scoped TensorProduct

noncomputable local instance primeResidue (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) := RingHom.toAlgebra PadicInt.toZMod

def HasPrimeFieldLift (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] [Module.Free (ZMod p) V]
    (_hV : Module.rank (ZMod p) V = 2) (ρ : GaloisRep ℚ (ZMod p) V) : Prop :=
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R (ZMod p)) (_ : IsScalarTower ℤ_[p] R (ZMod p))
      (_ : ContinuousSMul R (ZMod p))
      (W : Type) (_ : AddCommGroup W) (_ : Module R W)
      (_ : Module.Finite R W) (_ : Module.Free R W)
      (hW : Module.rank R W = 2) (σ : GaloisRep ℚ R W)
      (e : (ZMod p) ⊗[R] W ≃ₗ[ZMod p] V),
      IsHardlyRamified hpodd hW σ ∧ (σ.baseChange (ZMod p)).conj e = ρ

def PrimeFieldLifting : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (hpodd : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] [Module.Free (ZMod p) V]
    (hV : Module.rank (ZMod p) V = 2) (ρ : GaloisRep ℚ (ZMod p) V),
    ρ.IsIrreducible → IsHardlyRamified hpodd hV ρ →
    HasPrimeFieldLift p hpodd V hV ρ

def FreyLifting : Prop :=
  ∀ P : FreyPackage, 17 ≤ P.p →
    letI : Fact P.p.Prime := ⟨P.pp⟩
    let ρ := P.freyCurve.galoisRep P.p P.hppos
    ρ.IsIrreducible →
      HasPrimeFieldLift P.p P.hp_odd _ (FreyCurve.torsion_rank P) ρ
```

No theorem about every finite residue extension, odd p = 3, or arbitrary
residual module universe is required. Fixing a basis would allow `V` and
`W` to be coordinate modules; it saves no major mathematics and introduces
transport work, so keep the basis-free API.

Do not insist on `R = ℤ_[p]`: a characteristic-zero point of a deformation
ring may require a ramified finite coefficient extension. For a domain-valued
version, reuse `exists_domain_quotient` and `hardlyRamified_quotient` and
compose tensor base change. Asking for a domain strengthens the *witness*
condition; it is not by itself a logical weakening of the original theorem.
The existing quotient argument proves why it is sufficient to seek such a
witness. Exact residual conjugacy can subsequently be weakened to equality
of residual Frobenius traces outside a finite set, since that is its only use.

The obvious p-adic Tate module of the Frey curve does **not** close this:
Frey residual ramification disappears at primes dividing its discriminant
because valuations are divisible by p. Those primes can remain ramified in
the characteristic-zero Tate module. A hardly ramified lift must remove them.

### Restricted family contract: one companion, then just its trace consequence

A concrete sufficient replacement for the all-primes family is:

1. For the chosen lift σ (or its domain quotient), choose a finite free local
   domain B over `ℤ_[3]`, a free rank-two U, and η over B which is hardly
   ramified at 3. Include the topology and module-topology instances required
   by `Assembly/Inputs.lean:78`.
2. Choose coefficient embeddings for B and the p-adic lift into their
   algebraic closures. Give **one** field E, embeddings into these two
   closures, a finite exceptional set S, and common trace coefficients
   `a_q : E` for good q. No family at any other prime is needed.
3. Apply the proved three-adic trace theorem to η; injectivity of the E
   embedding forces `a_q = 1 + q`. Transport that equality to p, descend
   through the injective domain embedding, then reduce to `ZMod p`.

`TraceCompatiblePair` in the new
`FLT/Deformations/RepresentationTheory/TraceCompatiblePair.lean:24`
formalizes exactly the scalar content of step 2. Its theorem is:

```lean
-- E is a field; A,B are commutative rings; A is nontrivial.
-- φ : E →+* A, ψ : E →+* B, good : ι → Prop,
-- left : ι → A, right : ι → B.
theorem TraceCompatiblePair.transport_one_add
    (h : TraceCompatiblePair φ ψ good left right) (n : ι → ℕ)
    (hleft : ∀ i, good i → left i = 1 + n i) :
    ∀ i, good i → right i = 1 + n i
```

Take `ι = ℕ`, `n = id`, and `good q` to mean prime q ≥ 5,
q ≠ p, outside S. Traces can be defined by an `if hq : q.Prime`
branch, with arbitrary values at nonprimes. Step 2 needs only a field E;
the number-field hypothesis is needed to *construct* companions from
automorphic forms, not to transport an already common trace coefficient.

After composing with the established three-adic result, the needed family
consequence can be stated without E, embeddings, or a companion at all:

```lean
-- Same R,V,σ hypotheses as Family.lean:29-35, with p ≥ 17.
-- This is a consequence target; proving it includes the 3-adic step.
def IntegralTraceInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 17 ≤ p → ∀ (hpodd : Odd p)
    (R : Type) [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[p] R]
    (V : Type) [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (σ : GaloisRep ℚ R V),
    IsHardlyRamified hpodd hV σ → CofiniteFrobeniusTrace p σ
```

This universal `IntegralTraceInput` is still more than B4 needs. The smallest
useful construction boundary is **joint existence**: for each irreducible
Frey residual input, produce one lift satisfying both the lifting contract
and `CofiniteFrobeniusTrace P.p σ`. Put the latter inside the lift's
existential, or construct a companion for that selected witness. Do not
prove an arbitrary lifting theorem and then silently assume its arbitrary
chosen lift lies in the special class covered by a companion theorem.
Retain residual irreducibility/provenance through the domain quotient.
If the family theorem is restricted to absolutely irreducible lifts, this
retention and the absolute-irreducibility bridge become explicit obligations.

These statements require no characteristic-p domain pretending to embed in
characteristic zero. The earlier defect recorded in `docs/CORE_PLAN.md`
is repaired here: `Family.lean:30` now includes `Module.Free ℤ_[p] R`.
Do not copy the historical, weaker binder list from that document.

## Implemented prerequisite: residual absolute irreducibility

`HardlyRamified/AbsoluteIrreducibility.lean` proves that every irreducible
residual hardly ramified representation is absolutely irreducible, for every
odd prime and finite coefficient field in the existing contract. It derives
the rank-one fixed space from rational complex conjugation: the involution has
cyclotomic determinant minus one, and its fixed subspace is neither zero nor
the whole two-dimensional space. The residual characteristic is derived from
the p-adic algebra structure. No additional fixed-space, characteristic, or
absolute-irreducibility hypothesis is supplied by the caller.

`FLTTest/HardlyRamifiedAbsoluteIrreducibility.lean` audits this endpoint and
four supporting results. This supplies the absolute-irreducibility prerequisite
for unrestricted deformation representability. It does not prove irreducibility
after restricting to a cyclotomic extension, local-condition representability,
a characteristic-zero point, `lifts`, or compatible-family existence.
The three final arithmetic leaves are unchanged.

## Implemented connection: unrestricted universal deformation

`Deformations/HardlyRamifiedUniversal.lean` connects the residual
hardly ramified hypotheses to the existing de Smit–Lenstra construction.
It proves absolute irreducibility of the actual matrix representation,
constructs a universal unrestricted lift over the existing universal trace
ring, and derives corepresentability of the unrestricted deformation functor.
The residual p-adic algebra is the composite through the coefficient ring's
residue map. Absolute irreducibility is derived, not supplied as a new premise.

`FLTTest/HardlyRamifiedUniversal.lean` audits all three endpoints.
This does not assert that the universal representation itself satisfies
the hardly ramified local conditions, nor that the ring has a characteristic-zero
point with those conditions. The local-condition quotient, its required point,
and compatible-family existence remain open; the three final arithmetic
leaves are unchanged.

## Mathematical route and sources

### Blueprint scope, including its limitations

The authoritative source for this route is the LaTeX blueprint's **Chapter 4,
“An overview of the proof”**, `blueprint/src/chapter/ch04overview.tex`:

* §1, lines 10–43: potential modularity over a totally real **even-degree**
  extension, Galois/disjointness/unramifiedness conditions, Moret–Bailly,
  class field theory, automorphic induction, and Jacquet–Langlands.
* §2, lines 45–105: the precise S-good local conditions and modularity
  lifting; Skinner–Wiles reduction to minimal level followed by
  Taylor–Wiles–Kisin. Absolute irreducibility after restriction to the
  cyclotomic extension is a hypothesis, not a consequence of ordinary
  irreducibility that may be suppressed.
* §3, lines 107–122: Khare–Wintenberger lifting, compatible families using
  the Brauer induction trick cited as `blggt`, and specialization at 3.

**Chapter 6**, `ch06automorphicrepresentations.tex:1`, is explicitly about
*stating* the modularity lifting theorems. The quaternion-algebra miniproject
(`QuaternionAlgebraProject.tex:1`) explains finite-dimensional definite
quaternionic forms and Hecke algebras; the Hecke miniproject
(`HeckeOperatorProject.tex:1,24`) develops the double-coset operators.
Chapter 5's explicit quaternionic example is motivation, not a family
construction theorem.

The Verso blueprint was checked too:
`blueprint-verso/FLTBlueprint/Blueprint.lean:35` includes only Levels 1–3,
with the three chapter files listed in `blueprint-verso/FLTBlueprint.lean`.
It currently has no Chapter 4 lifting/family development. Do not cite a
nonexistent Verso proof or infer completion from a blueprint label.

`FLT.bib:321` identifies Khare–Wintenberger, *Serre's modularity conjecture II*,
Invent. Math. 178 (2009), 505–586, DOI `10.1007/s00222-009-0206-6`.
Chapter 4:88 explicitly says its modularity-lifting references are near
matches: Taylor's theorem assumes splitting at ℓ, and Gee's assumes a
stronger residual image. The bibliography search did not find a `blggt`
entry. Resolve that citation and pin exact theorem hypotheses in S0 below.
No external paper theorem number beyond what the blueprint names is
asserted to have been checked in this investigation.

The brief's **Ramakrishna/Böckle** description is a proposed expansion of
the deformation part of Khare–Wintenberger, not a detailed proof found in
these chapters: neither name appeared in the blueprint search. S0 must
select an exact theorem and account for its hypotheses before arithmetic
implementation. This is a genuine mathematical design gate.

### Lifting: what a proof must construct

Start from an odd, absolutely irreducible rank-two residual representation.
Cyclotomic determinant supplies oddness, but formal complex-conjugation
and eigenspace arguments must connect it to the representation API. The
available absolute-irreducibility adapter requires that eigenspace input.
Irreducibility over ℚ does not automatically give irreducibility upon
restriction to `F(ζ_p)`; handle exceptional images and the field choice.

Construct a determinant-fixed deformation problem with local conditions:
unramified outside `{2,p}`, finite-flat at p at **every open coefficient
quotient**, and the specified rank-one quotient at two. Compute tangent
and obstruction spaces via continuous cohomology and Selmer conditions.
Representability alone permits a ring with no characteristic-zero point.

Ramakrishna-style auxiliary primes kill dual Selmer obstructions under the
appropriate residual-image hypotheses. Such an auxiliary-prime lift may
have **extra ramification**, so it is not yet `lifts`. A Böckle-style
dimension/nonvanishing argument, potential modularity, and finiteness or
level control must produce a characteristic-zero point of the *required*
local deformation problem. Prove the hypotheses of the selected theorem,
including the small/dihedral-image cases, rather than adding “adequate”
as an undocumented assumption on all Frey representations.

Extract a finite p-adic coefficient field, a stable lattice over a finite
free local order, and residual identification. Reconstruct the precise
`IsHardlyRamified.isTameAtTwo` quotient; inertia trace 2 alone is not its
entire definition. Quotient/normalization and finite-flat transport must
preserve the same chosen residual representation.

### Modularity and families: shared infrastructure, not a second shortcut

Over a totally real even-degree F, use the quaternion algebra ramified at
all infinite and no finite places. Weight two, trivial central character,
and the blueprint's S-level conditions suffice. Build localized Hecke
modules and their Galois representations, the map from the local-condition
deformation ring to the Hecke algebra, and Taylor–Wiles auxiliary levels.
Verify the actual rank, freeness, support, local-ring and dimension inputs
of the existing abstract patching theorem. Its conclusion is **kernel
contained in the nilradical**, not an unconditional ring isomorphism.
Explain why that support statement gives the desired modularity at points.

Moret–Bailly supplies a field/curve with prescribed local behavior, allowing
a switch through an induced residual representation. Automorphic induction,
Jacquet–Langlands, cyclic base change/descent and modularity lifting supply
potential modularity. The lift's Frobenius eigenvalues then live in an
algebraic Hecke coefficient field. Attach representations at p and 3 to the
same automorphic data and descend from F to ℚ using Brauer induction and
solvable descent, as in Chapter 4 §3.

A virtual character identity from Brauer induction is not yet a genuine
continuous rank-two representation. Prove effectiveness, compatibility,
descent, determinant, and the required local conditions. Good-prime trace
equalities do not by themselves give the finite-flat integral model at 3
or the unramified square-trivial quotient at two. Those are separate
local-global compatibility/integral-model obligations. Restricting to two
primes saves family bookkeeping, not these global theorems.

## Repository inventory: source evidence, not blanket trust certification

All paths below start at `FLT/`. “Body present” means the declaration was
inspected and contains a proof; its whole dependency closure was not freshly
certified here. An assumption encoded in a structure field is still an input.

| Component and location | Available now; what is missing |
|---|---|
| `Deformations/Representable.lean:38` | General deformation representability has a body using de Smit–Lenstra reconstruction. It requires absolute irreducibility; no local conditions or characteristic-zero point follow. |
| `Deformations/DeSmitLenstra/UniversalTraceLift.lean:43` | Universal trace lift construction has a body; reuse the representation-ring/Morita infrastructure. |
| `Deformations/Representable.lean:89,104,114` | S-good and narrow S-good functors are defined. `isCorepresentable_narrowSLiftFunctor` is **sorried at 116**; its universal ring at 119 depends on it. |
| `GaloisRepresentation/HardlyRamified/AbsIrredAdapter.lean:29,45` | Proved adapter from a rank-one fixed space. Does not construct complex conjugation with that property or cyclotomic-restriction irreducibility. |
| `Deformations/RepresentationTheory/GaloisRep.lean:396` | Flatness API uses every open coefficient ideal. Residual finite flatness alone cannot replace this. |
| `PoitouTate.lean:46,71,87` | Carrier-data scaffold; `greenbergWilesOrderFormula` projects the supplied `orderFormula`. No arithmetic duality/actual Selmer dimension calculation is constructed. |
| `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` | Continuous-cochain foundations exist. Arithmetic local/global duality and the deformation local-condition computations remain obligations. |
| `Patching/Module.lean:247,533,634`; `Patching/Algebra.lean` | Actual patching modules/algebras, patching-system class and freeness results have bodies. These are reusable algebra. |
| `Patching/System.lean:422`; `Patching/REqualsT.lean:86` | `support_eq_top` and `ker_RtoT_le_nilradical` have bodies; no supplied Taylor–Wiles primes, arithmetic modules or verified numerical hypotheses. |
| `QuaternionAlgebra/NumberField.lean:67,80` | Rigidification class and adelic matrix equivalence. Existence of every required global D and level datum is not given by merely assuming that class. |
| `AutomorphicForm/QuaternionAlgebra/Basic.lean:109,397,575` | Weight-two forms, level structures and level-form spaces are implemented. |
| `AutomorphicForm/QuaternionAlgebra/FiniteDimensional.lean:53` | `finite_doubleCoset` has a proof; supplies the finite level-space infrastructure. |
| `AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:878,1092` | Concrete Hecke algebra and anemic algebra; operator constructions exist in Abstract/Local/Concrete. |
| `AutomorphicForm/QuaternionAlgebra/InnerProduct.lean:480,620,844` | Eigenforms, eigenspace decomposition and tensor/product description have bodies. These are not Galois attachment. |
| `GaloisRepresentation/Automorphic.lean:72` | `IsAutomorphicOfLevel` defines the intended trace/determinant relation to weight-two Hecke eigenvalues. |
| Same file:139,237 | `cyclic_base_change` and `quadratic_cm_automorphic_induction` are **sorried at 196,273**. |
| `GaloisRepresentation/Attachment.lean:135,169` | Attachment predicate and conversion to automorphy have bodies. |
| Same file:209,249,291,335 | Existence of attached representations, integral models, tame rank-one quotients, flat integral models are **sorried at 230,272,314,362**. |
| `CyclicBaseChange/Statements.lean:281,379,405,431` | Satake existence, base change, descent and twisting character endpoints are **sorried at 288,392,418,446**. Their statements are not established base change. |
| `MoretBailly.lean:87` | Specialized existence theorem is **sorried at 107**. |
| `Deformations/RepresentationTheory/GaloisRepFamily.lean:38,58` | Family type and compatibility predicate only; no companion construction. |
| `GaloisRepresentation/HardlyRamified/Lift.lean:37,48`; `Family.lean:37,68` | The two target declarations end in `sorry`. |
| `GaloisRepresentation/HardlyRamified/B5Inputs.lean:52,106,160` | Domain quotient, flatness under quotient and hardly-ramified transport have bodies. Reuse, do not redispatch. |
| Same file:226,240,261,288 | Trace/base-change/conjugacy, coefficient embedding injectivity and family trace transfer have bodies. |
| `GaloisRepresentation/HardlyRamified/Chebotarev/FrobeniusTraces.lean:262` | Frobenius trace reducibility criterion has a body; no new Chebotarev project needed for this plan. |
| `Assembly/PrimePowerFinal.lean:25`; `Assembly/PrimePowerSortingProof.lean` | Current assembly supplies the three-adic trace from full sorting. Do not import the old `three_adic` endpoint to implement this route. |

Text searches found no implemented Khare–Wintenberger/Ramakrishna/Böckle
endpoint or construction connecting arithmetic deformation rings to the
existing patching system. Absence is a scoped search finding, not a claim
about every external library. Searches of `Deformations`, `Patching`,
`AutomorphicForm`, `QuaternionAlgebra` found only the one actual admission
in `Representable.lean`; occurrences of “admits” in comments are not proofs.
This does not certify that their imported dependencies are all clean.

## Work packages and dependency graph

Estimates below are **additional** code and hours, including review. Large
packages are programs to split after their contracts pass review, not tasks
to hand to a capped worker. The hours include statement/proof design; a line
count is not a mathematical difficulty measure.

| ID | Deliverable and acceptance evidence | Dependencies | Lean lines | Worker-hours |
|---|---|---|---:|---:|
| S0 | Source/hypothesis ledger for exact lifting, modularity and Brauer-descent theorems; reconcile Chapter 4 reference gaps | none | 0 | 80–160 |
| R0 | Frey residual representation to odd/absolute-irreducibility and coefficient API; distinguish cyclotomic restriction | S0 | 1k–3k | 150–400 |
| D1 | Determinant-fixed local deformation conditions; representability, flat/tame quotient components and local dimensions | S0, R0 | 20k–40k | 2k–5k |
| D2 | Actual arithmetic duality, Selmer/dual Selmer formula, auxiliary-prime existence with image hypotheses | S0, R0 | 15k–35k | 1.8k–4k |
| A1 | Required quaternionic Hecke/Galois attachment and local-global/integral compatibility; induction, JL and base change | S0 | 30k–70k | 3.5k–9k |
| T1 | Arithmetic Taylor–Wiles systems, numerical hypotheses and R-to-T support; minimal/nonminimal modularity lifting | D1, D2, A1 | 15k–35k | 1.8k–4.5k |
| P1 | Moret–Bailly construction and field selection; auxiliary-curve switch proving potential modularity | R0, A1, T1 | 12k–30k | 1.5k–4k |
| K1 | Khare–Wintenberger lifting: characteristic-zero point of the desired deformation problem and its integral residual realization | D1, D2, P1 | 8k–20k | 1k–2.5k |
| C1 | Common coefficient field, p/3 attachments, effective Brauer/solvable descent to ℚ, hardly ramified integral 3-model | A1, P1, K1 | 15k–35k | 1.8k–4.5k |
| I1 | Witness-preserving trace reduction, Frey-only assembly and dependency audit | K1, C1, L1–L3 | 1k–3k | 120–360 |

```text
S0 -> R0 -> D1 -----> T1 -----> P1 -----> K1 -----> C1
           D2 -----> T1        ^         ^          ^
S0 -> A1 ----------> T1 -------|         |          |
      A1 --------------------> P1       |          |
      A1 ----------------------------------------> C1
           D1 + D2 --------------------> K1
                              P1 ----------------> C1
L1 -> L2 ----------------------------------------> I1
L3 + K1 + C1 ------------------------------------> I1 -> restricted FLT assembly
```

R0 is also a dependency of P1 (as in the table). T1 is a theorem conditional
on **residual automorphy**, not on the global lift K1 is to construct; P1
uses the auxiliary elliptic curve's existing Tate module. This prevents the
otherwise easy circularity “construct a lift using its own modularity”.
The full all-primes `mem_isCompatible` and all-finite-fields `lifts` are
optional extensions after I1, not hidden requirements of this estimate.

### Stopping gates

1. **S0 before arithmetic dispatch:** identify exact theorem pages and all
   residual-image, local, coefficient and ramification hypotheses. Resolve
   the unramified-versus-split prime issue and the missing `blggt` citation.
   If no source covers the needed case, keep that as research, not a Lean
   task with an invented deadline. Reestimate the affected packages.
2. **R0/D1:** exhibit the actual oddness bridge and an admissible local
   finite-flat deformation problem. Check that the condition at two gives
   the quotient demanded by `Defs.lean`, not just its trace shadow.
3. **D2/T1:** instantiate arithmetic cohomology and every patching-system
   input with actual objects. A supplied `orderFormula` or nonzero-module
   field is not proof that the object exists. Auxiliary primes must satisfy
   the Chebotarev/image constraints used in the selected theorem.
4. **K1:** demonstrate a characteristic-zero point with no unwanted auxiliary
   ramification, a finite free coefficient ring, and the chosen residual
   identification. A prorepresenting ring or ramified auxiliary lift fails
   this gate. Do not drop `Module.Free ℤ_[p] R`.
5. **C1:** show a genuine rank-two companion over ℚ, a single common trace
   field, and the integral hardly-ramified 3-model. A virtual representation,
   form over F only, or good-prime trace attachment alone fails this gate.
6. **I1:** prove the new conditional adapter first, then fill its premises
   with K1/C1. Run the recursive final dependency audit after rewiring.
   Remaining Mazur dependence must remain explicit. Never route through
   `lifts`, `mem_isCompatible`, or B4's unconditional proof to prove their
   replacements.

## First three dispatchable leaves (each at most 500 lines)

### L1 — trace transfer between two specializations (delivered here)

File: `FLT/Deformations/RepresentationTheory/TraceCompatiblePair.lean`.
Contract: the predicate and `transport_one_add` displayed above. Import
only Mathlib ring/field APIs. Recover `a i = 1 + n i` by injectivity of φ,
then apply ψ. All good-index restrictions remain explicit; no hidden
unramifiedness, irreducibility or family-existence assumption.

Budget: **40–100 lines, 1–3 hours**. Dependency: none. Consumer: L2 and C1's
two-prime trace boundary. Acceptance: build, targeted lint, and dependency
list containing only `propext`, `Classical.choice`, `Quot.sound` (or a subset).
This is algebraic interface work; it removes no arithmetic admission.

### L2 — project a compatible family to its two trace functions

New file: `FLT/Deformations/RepresentationTheory/FamilyTracePair.lean`.
Budget: **100–250 lines, 4–10 hours**. Dependencies: L1 and the existing
family definition. Imports should avoid Lift/Family admitted endpoints.

Define total `frobTrace σ q` using the prime-test branch described above.
The signature sketch, with `hℓ : Fact ℓ.Prime`, `hp : Fact p.Prime`, is:

```lean
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

Bind `E : Type` with `[Field E] [NumberField E]`, and primes explicitly.
Extract S and `Pv` from compatibility; use `-(Pv v).coeff 1` at prime
indices and 0 elsewhere. The existing `B5Inputs.trace_eq_neg_coeff` and
`prime_not_mem` show the calculation. Reuse them or factor them into a
small neutral module if importing B5 is too broad; do not duplicate the
Chebotarev proof. Its present `compatible_trace` already performs the scalar
argument for whole families, so this leaf is a **new interface projection**,
not a missing proof of that existing theorem.

Acceptance: transport from ℓ = 3 recovers the p-trace consequence under the
given family premise; no family is constructed. Audit both new declarations.

### L3 — conditional Frey-only trace assembly

New file: `FLT/Assembly/FreyTraceInput.lean`. Budget: **120–300 lines,
5–12 hours**. Dependencies: existing Frey determinant/rank, Chebotarev
criterion and conditional Mazur assembly. Independent of L1/L2 arithmetic.

Add `CofiniteFrobeniusTrace` and `FreyResidualTraceInput` exactly as above;
then prove these statement sketches:

```lean
theorem FLT.Bosses.B4_of_freyResidualTrace
    (htrace : FreyResidualTraceInput) : FLT.Bosses.B4

theorem flt_of_freyResidualTrace
    (hmazur : FLT.Assembly.MazurTorsionExclusion)
    (htrace : FreyResidualTraceInput) : FermatLastTheorem
```

For each P and hp17, install `Fact P.p.Prime`, the canonical p-adic algebra
on `ZMod P.p`, and its local-hom instance as in `Assembly/PrimeField.lean`.
Assume irreducibility, extract S from htrace, and apply the existing trace
criterion with `P.hp5`, Frey rank and determinant. Then use
`B3_of_torsionExclusion`, `B3_implies_B2`, and `B2_implies_B1`.

Acceptance: the conditional endpoints have clean dependency lists and
explicit hmazur/htrace premises. Do not modify `FermatsLastTheorem.lean`
until those premises have proofs. The declaration must not use
`not_isIrreducible_of_prime_field`, which already consumes the missing inputs.

## Validation and reproduction

Source inventory can be rerun at the pinned baseline with:

```sh
rg -n 'not_isIrreducible_of_prime_field|mem_isCompatible|\.lifts' FLT
rg -n -i 'deformation|patching|quaternion|automorphic|hecke' FLT
rg -n 'sorry|^axiom' FLT/Deformations FLT/Patching FLT/AutomorphicForm \
  FLT/QuaternionAlgebra FLT/GaloisRepresentation/Attachment.lean \
  FLT/GaloisRepresentation/Automorphic.lean FLT/CyclicBaseChange/Statements.lean
rg -n -i 'khare|ramakrishna|b.ckle|blggt|taylor|kisin' blueprint blueprint-verso
```

Build only one module at a time under the 10 GB cap:

```sh
lake build FLT.Deformations.RepresentationTheory.TraceCompatiblePair
lake lint -- --no-build FLT.Deformations.RepresentationTheory.TraceCompatiblePair
```

The external audit file imports that module and runs
`#print axioms GaloisRepresentation.TraceCompatiblePair.transport_one_add`.
Checked **2026-09-28 10:54 UTC**: the module build and targeted lint passed;
the printed dependency list was exactly
`[propext, Classical.choice, Quot.sound]`. The new file is 43 lines with
maximum width 83 and no prohibited proof shortcuts. `lake env lean FLT.lean`
passed; the umbrella contains 988 C-sorted imports matching all 988 `.lean`
files under `FLT/`. The complete definition blocks for
`CofiniteFrobeniusTrace`, `FreyResidualTraceInput`, `HasPrimeFieldLift`,
`PrimeFieldLifting`, `FreyLifting`, and `IntegralTraceInput` were extracted
to `/tmp/lf0-audit/Statements.lean` and elaborated without warnings. The L2/L3
theorem sketches remain proposed work. The full existing FLT library is not
claimed newly rebuilt by this delivery. `FLTTest/AssemblyAxioms.lean:38`
records the expected three arithmetic leaves; source inspection alone is
not a fresh execution of that guard. Final verification results and local
commit identifiers are recorded in `LAST.txt`.
