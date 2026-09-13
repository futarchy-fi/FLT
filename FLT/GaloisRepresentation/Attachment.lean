/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.Automorphic

/-!
# Attachment of Galois representations to quaternionic eigensystems

This file states, in the weakest form that the rest of the project needs, the theorem that
attaches a two-dimensional `p`-adic Galois representation to a weight-2 trivial-character
eigensystem on a totally definite quaternion algebra of discriminant `1` over a totally real
number field `F` of even degree.

The input is exactly the input consumed by `GaloisRep.IsAutomorphicOfLevel`
(`FLT/GaloisRepresentation/Automorphic.lean`): an `ℤ_[p]`-algebra homomorphism
`π : HeckeAlgebra D ⟨_, S, ∅, 1, _, hp⟩ →ₐ[ℤ_[p]] A` out of the quaternionic Hecke algebra of
level `U₁(S)` and weight `2`. The instance and hypothesis shape below is copied verbatim from
`GaloisRep.IsAutomorphicOfLevel` so that the two statements compose without any coercion; the
composition is witnessed by `GaloisRep.isAutomorphicOfLevel_of_isAttachedAtGoodPrimes`.

## Main declarations

* `GaloisRep.IsAttachedAtGoodPrimes` -- the good-primes-only compatibility predicate: for every
  finite place `v` of `F` with `v ∤ p` and `v ∉ S`, the representation `ρ` is unramified at `v`,
  `det ρ(Frob_v) = N(v)` and `tr ρ(Frob_v) = π(T_v)`.
* `GaloisRep.isAutomorphicOfLevel_of_isAttachedAtGoodPrimes` -- the composition lemma (proved).
* `exists_galoisRep_isAttachedAtGoodPrimes` -- clause (W): the attachment statement itself.
* `exists_integralModel_of_isAttachedAtGoodPrimes` -- clause (I): integrality.
* `exists_tameRankOneQuotient_of_isAttachedAtGoodPrimes` -- clause (T): tame rank-1 quotient at
  the places of `S`.
* `exists_flatIntegralModel_of_isAttachedAtGoodPrimes` -- clause (Bp): flatness at `p`.

Nothing here is an `axiom`: all four clauses are stated with unproved bodies.

## Scope

Deliberately weak, matching `GaloisRep.IsAutomorphicOfLevel`: weight `2` only, trivial character,
totally definite `D` of discriminant `1`, even-degree totally real `F`, level `U₁(S)`, and
**good primes only** (`v ∉ S`, `v ∤ p`). No local-Langlands / Weil--Deligne matching at the bad
places is asserted, and no full compatible-family statement is made here (that lives at
`FLT/GaloisRepresentation/HardlyRamified/Family.lean`).

The good-primes-only scope is a *consumer-wiring checkpoint*: no wiring into `Patching`/`REqualsT`
exists today against which to check sufficiency, so the scope must be re-validated when the
patching consumer is drafted.

## Absorption ledger (mandatory; hub-lsb1u.10.3 §3, finalized by hub-lsb1u.10.4 ruling 6)

Per the ratified JL Route A rider, an absorbing statement must enumerate the mathematics it
hides. `exists_galoisRep_isAttachedAtGoodPrimes` hides the following five items.

1. **Jacquet--Langlands transfer direction, and the load-bearing citation.**
   The literature theorem takes a `GL₂` *Hilbert* eigenform as input, whereas the input here is a
   *quaternionic* Hecke eigensystem. Stating attachment quaternionically therefore silently
   absorbs the transfer direction *quaternionic eigensystem → Hilbert eigenform*. Because `F`
   has even degree and `D` is **totally definite** (ramified at every infinite place), there is
   no split infinite place, hence no Shimura curve and no cohomological realization: Carayol's
   construction is structurally inapplicable to this `D`. The primary, load-bearing citation is
   therefore **Taylor, "On Galois representations associated to Hilbert modular forms",
   Invent. Math. 98 (1989), 265--280**, which closed the even-degree case by congruences and
   pseudo-representations. **Carayol, Ann. Sci. ENS 19 (1986), 409--468** is a *secondary,
   upstream* input (Taylor's congruence argument consumes it; it remains the `ℓ ≠ p`
   local-global reference). Both are pre-1990, so the `knownin1980s` policy is unaffected.
   Double-count rule: the JL transfer content is credited once against hub-lsb1u.4 and marked
   `[shared:.4]` here -- do not count it again.
2. **Multiplicity-one absorption.** The passage from an eigensystem to a well-defined
   representation absorbs strong multiplicity one / quaternionic multiplicity one. That content
   is **owned by node G16** (minted by `cartography/panel/greps-adjudication.md`, ruling 2) and
   is not restated here; it feeds this node and G12.
3. **Coefficient-bridge non-canonicity.** The identification of the `ℤ_[p]`-valued Hecke
   eigensystem with a system of algebraic numbers, and its embedding into `A`, is **not
   canonical**: it depends on a choice of embedding of the Hecke field into `ℚ_[p]ᵃˡᵍ`. The
   integrality anchor is Shimura's parallel-weight integrality for Hilbert modular forms; the
   statement below quantifies existentially over `ρ` precisely so that no canonical choice is
   claimed.
4. **Norm-factoring exclusion.** Eigensystems whose associated representation factors through a
   norm / is a twist of a one-dimensional character composed with the norm are *excluded* from
   the scope of this statement; nothing below asserts irreducibility, and no consumer may infer
   it from these clauses.
5. **Automorphic induction is OUT OF SCOPE.** Attachment by automorphic induction from a CM /
   quadratic extension is **not** claimed here; that content is **owned by CBC S6**
   (`cartography/cbc-reconciled.md`). The note is recorded to preempt re-importing it into this
   node.

## Non-vacuity obligation

TODO (hub-lsb1u.10.4 ruling 4): nothing in this repository witnesses
`GaloisRep.IsAutomorphicOfLevel` -- or `GaloisRep.IsAttachedAtGoodPrimes` -- as satisfiable for
*any* `ρ`. An explicit witness is
owed (expected route: the Galois representation of a known modular elliptic curve, once enough
wiring exists). The obligation **blocks axiom-pinning of this node, not its drafting**: the
clauses below may be stated and consumed as unproved theorems, but none of them may be converted
into an `axiom` until a witness exists, on pain of pinning a vacuous or inconsistent assumption.

## References

* Taylor, Invent. Math. 98 (1989), 265--280 -- primary.
* Carayol, Ann. Sci. ENS 19 (1986), 409--468 -- secondary/upstream.
* Saito, Compositio Math. 145 (2009) and Breuil, Bull. SMF 127 (1999) -- for clause (Bp) only;
  both are **post-1990**, see the marker on that declaration.
-/

@[expose] public section

open scoped TensorProduct

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra WeightTwoAutomorphicForm

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u -- u for number field / quaternion algebra.

set_option linter.unusedVariables false in
/--
`GaloisRep.IsAttachedAtGoodPrimes p hp S D π ρ` says that the two-dimensional Galois
representation `ρ` of the absolute Galois group of the totally real field `F` is compatible with
the weight-2 trivial-character quaternionic eigensystem `π` **at the good primes only**: for every
finite place `v` of `F` with `v ∤ p` and `v ∉ S`,

* `ρ` is unramified at `v`;
* `det ρ(Frob_v) = N(v)` (arithmetic Frobenius), i.e. `det ρ` is the cyclotomic character;
* `tr ρ(Frob_v) = π(T_v)`.

This is the body of `GaloisRep.IsAutomorphicOfLevel` with the quaternion algebra `D` and the
eigensystem `π` made explicit instead of existentially quantified; see
`GaloisRep.isAutomorphicOfLevel_of_isAttachedAtGoodPrimes`.
-/
@[nolint unusedArguments]
def GaloisRep.IsAttachedAtGoodPrimes
    -- `F` is a totally real field
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
    [ContinuousSMul ℤ_[p] A]
    -- `V` is the rank 2 free `A`-module on which the Galois group will act
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    -- `S` is the level of the modular form
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    -- `D` is a totally definite quaternion algebra over `F` of discriminant 1
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    -- `π` is an `A`-valued weight 2 eigensystem of level `U₁(S)`, i.e. a `ℤ_[p]`-algebra map
    -- out of the `ℤ_[p]`-Hecke algebra for `(D, S)`
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] A)
    -- `ρ` is the Galois representation
    (ρ : GaloisRep F A V) : Prop :=
  -- for all good primes `v` of `F`
  ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
    -- `ρ` is unramified at `v`,
    ρ.IsUnramifiedAt v ∧
    -- the det of `ρ(Frobᵥ)` (arithmetic Frobenius) is `N(v)` (i.e. `det(ρ) = cyclo`)
    (ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
    -- and the trace of `ρ(Frobᵥ)` is the eigenvalue of the form at `Tᵥ`
    LinearMap.trace A V (ρ.toLocal v (Frob v)) =
      π (HeckeAlgebra.T (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ v hvS (by simp))

/--
A representation attached to a quaternionic eigensystem at the good primes is automorphic of the
corresponding level. This is the composition lemma: it shows that `IsAttachedAtGoodPrimes` is
literally the body of `GaloisRep.IsAutomorphicOfLevel`, so the attachment clauses below feed the
automorphy predicate with no coercion.
-/
theorem GaloisRep.isAutomorphicOfLevel_of_isAttachedAtGoodPrimes
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
    [ContinuousSMul ℤ_[p] A]
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    (hV : Module.finrank A V = 2)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] A)
    (ρ : GaloisRep F A V) (hρ : ρ.IsAttachedAtGoodPrimes p hp S D π) :
    ρ.IsAutomorphicOfLevel p hp hV S := by
  refine ⟨D, ‹DivisionRing D›, ‹Algebra F D›, ‹IsQuaternionAlgebra F D›,
    ‹IsQuaternionAlgebra.NumberField.WithRigidification F D›, π, ?_⟩
  exact hρ

/--
**Attachment, clause (W): the weakest attachment statement, good primes only.**

Let `F` be a totally real number field, `p` a prime with `hp`, `D/F` a totally definite
quaternion algebra of discriminant `1`, `S` a finite set of finite places of `F`, and let
`π : HeckeAlgebra D ⟨_, S, ∅, 1, _, hp⟩ →ₐ[ℤ_[p]] A` be a weight-2 trivial-character
quaternionic eigensystem with values in the topological `ℤ_[p]`-algebra `A`. Then for any rank-2
free `A`-module `V` there exists a Galois representation `ρ : GaloisRep F A V` which is
compatible with `π` at all good primes.

Only the good primes are constrained: `v ∉ S` and `v ∤ p`. Nothing is asserted at the bad
places, nor about irreducibility, nor about canonicity of `ρ` (see ledger item 3).

This is node **G3** of `cartography/galois-reps-reconciled.md`, clause (W). It is an absorbing
statement: see the module docstring's five-item absorption ledger, and the non-vacuity obligation
recorded there. Primary citation: Taylor 1989 (Invent. Math. 98, 265--280); Carayol 1986
(Ann. Sci. ENS 19, 409--468) is upstream input only.
-/
-- TODO (non-vacuity obligation, `cartography/panel/greps-adjudication.md` ruling 4):
-- no witness of `GaloisRep.IsAutomorphicOfLevel`, hence none of `IsAttachedAtGoodPrimes`, exists
-- anywhere in this repository, so nothing yet shows this statement is non-vacuous. An explicit
-- witness is owed (expected route: a known modular elliptic curve's representation). This blocks
-- turning the clause below into an `axiom`; it does not block stating or consuming it.
theorem exists_galoisRep_isAttachedAtGoodPrimes
    -- let `F` be a totally real number field of even degree
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    -- let `p` be a prime
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    -- let `A` be the topological `ℤ_[p]`-algebra of coefficients
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
    [ContinuousSMul ℤ_[p] A]
    -- let `V` be a rank 2 free `A`-module
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    (hV : Module.finrank A V = 2)
    -- let `S` be a finite set of finite places of `F`
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    -- let `D` be a totally definite quaternion algebra over `F` of discriminant 1
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    -- and let `π` be an `A`-valued weight 2 eigensystem of level `U₁(S)`
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] A) :
    -- then there is a Galois representation attached to `π` at the good primes
    ∃ ρ : GaloisRep F A V, ρ.IsAttachedAtGoodPrimes p hp S D π :=
  sorry

/--
**Attachment, clause (I): integrality.**

A representation attached to a `ℚ_[p]ᵃˡᵍ`-valued quaternionic eigensystem at the good primes
descends to an integral model: there is a local domain `R`, finite free over `ℤ_[p]` and
topologically embedded in `ℚ_[p]ᵃˡᵍ`, a rank-2 free `R`-module `V₀` and a representation
`ρ₀ : GaloisRep F R V₀` whose base change to `ℚ_[p]ᵃˡᵍ` is `ρ`.

The integral-model shape is the one consumed by `cyclic_base_change`'s `hρflat` hypothesis
(`FLT/GaloisRepresentation/Automorphic.lean`), so that clause (Bp) below is exactly this clause
plus flatness.

Mathematically this is the integrality of the Hecke eigenvalues: the eigensystem takes values in
the ring of integers of a finite extension of `ℚ_[p]`. The integrality anchor is Shimura's
parallel-weight integrality (ledger item 3); note that the descent is *not* canonical, since it
depends on the chosen embedding of the Hecke field into `ℚ_[p]ᵃˡᵍ`.
-/
theorem exists_integralModel_of_isAttachedAtGoodPrimes
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    {V : Type} [AddCommGroup V] [Module (ℚ_[p]ᵃˡᵍ) V]
      [Module.Finite (ℚ_[p]ᵃˡᵍ) V] [Module.Free (ℚ_[p]ᵃˡᵍ) V]
      (hV : Module.finrank (ℚ_[p]ᵃˡᵍ) V = 2)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] (ℚ_[p]ᵃˡᵍ))
    (ρ : GaloisRep F (ℚ_[p]ᵃˡᵍ) V) (hρ : ρ.IsAttachedAtGoodPrimes p hp S D π) :
    -- there's an integral model ρ₀ of ρ
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[p] R) (_ : IsLocalRing R) (_ : IsDomain R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R) (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R (ℚ_[p]ᵃˡᵍ)) (_ : IsScalarTower ℤ_[p] R (ℚ_[p]ᵃˡᵍ))
      (_ : ContinuousSMul R (ℚ_[p]ᵃˡᵍ))
      (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
      (_ : Module.Free R V₀) (_hV₀ : Module.rank R V₀ = 2)
      (ρ₀ : GaloisRep F R V₀)
      (r₀ : (ℚ_[p]ᵃˡᵍ) ⊗[R] V₀ ≃ₗ[ℚ_[p]ᵃˡᵍ] V),
    (ρ₀.baseChange (ℚ_[p]ᵃˡᵍ)).conj r₀ = ρ :=
  sorry

/--
**Attachment, clause (T): tame rank-1 quotient at the places of `S`.**

At each place `w ∈ S` (so `w ∤ p`, the level being prime to `p`), the restriction of an attached
representation to a decomposition group at `w` admits a rank-1 quotient on which the inertia acts
through a tamely ramified character. This is the local shape forced by the level `U₁(S)`: the
automorphic forms caught by that level are, at each `w ∈ S`, either Steinberg or a principal
series `π(χ₁, χ₂)` with `χᵢ` tame and `χ₁χ₂` unramified.

The conclusion is stated in exactly the shape of `cyclic_base_change`'s `hρtame` hypothesis
(`FLT/GaloisRepresentation/Automorphic.lean`), so that it can be fed to that theorem without
coercion.

Note that this clause is *not* part of the good-primes compatibility: it is a separate
consumer-forced clause (node **G4** of `cartography/galois-reps-reconciled.md`), stated here
because the same literature theorem supplies it.
-/
theorem exists_tameRankOneQuotient_of_isAttachedAtGoodPrimes
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    {V : Type} [AddCommGroup V] [Module (ℚ_[p]ᵃˡᵍ) V]
      [Module.Finite (ℚ_[p]ᵃˡᵍ) V] [Module.Free (ℚ_[p]ᵃˡᵍ) V]
      (hV : Module.finrank (ℚ_[p]ᵃˡᵍ) V = 2)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    -- the level is prime to `p`
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] (ℚ_[p]ᵃˡᵍ))
    (ρ : GaloisRep F (ℚ_[p]ᵃˡᵍ) V) (hρ : ρ.IsAttachedAtGoodPrimes p hp S D π) :
    ∀ w ∈ S, ∃ (q : V →ₗ[ℚ_[p]ᵃˡᵍ] ℚ_[p]ᵃˡᵍ)
      -- i.e. there's a surjection q : V → Q_p-bar
      (_ : Function.Surjective q)
      -- and a 1-d character of Gal(F_w-bar/F_w)
      (δ : GaloisRep (w.adicCompletion F) (ℚ_[p]ᵃˡᵍ) (ℚ_[p]ᵃˡᵍ)),
      -- such that δ is tamely ramified
      localTameAbelianInertiaGroup w ≤ δ.ker ∧
      -- and q is Gal(F_w-bar/F_w)-equivariant
      ∀ g : Γ (w.adicCompletion F), ∀ x : V, q ((ρ.toLocal w) g x) = δ g (q x) :=
  sorry

/--
**Attachment, clause (Bp): flatness at `p`.**

MODERN ASSUMPTION (post-1990). This clause is **not** available from the pre-1990 literature.
The applicable references are **Saito, Compositio Math. 145 (2009)** (local-global compatibility
at `p`) and **Breuil, Bull. SMF 127 (1999)** (weight-2 flatness), both post-1990. Carayol 1986 is
not an alternative here: his good-reduction models come from Shimura curves, which require a split
infinite place, whereas `D` is totally definite. Consequently this clause sits in the **same
ledger class as nodes G10 and G11** (the Khare--Wintenberger / BLGGT content), not in the
`knownin1980s` class that clauses (W), (I) and (T) belong to. Adjudicated by
`cartography/panel/greps-adjudication.md`, ruling 1; see also
`cartography/galois-reps-reconciled.md` §4.1. Do not reopen a Carayol+Raynaud 1980s route for
totally definite `D`.

Statement: when the level `S` is prime to `p`, the integral model of clause (I) can be chosen so
that it is furthermore flat (Barsotti--Tate) at every place of `F` dividing `p`. The conclusion is
verbatim the `hρflat` hypothesis of `cyclic_base_change`, and is what the `IsHardlyRamified`
consumers (`FLT/GaloisRepresentation/HardlyRamified/`) require.
-/
theorem exists_flatIntegralModel_of_isAttachedAtGoodPrimes
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    (p : ℕ) [Fact p.Prime] (hp : 2 < Module.finrank F (CyclotomicField p F))
    {V : Type} [AddCommGroup V] [Module (ℚ_[p]ᵃˡᵍ) V]
      [Module.Finite (ℚ_[p]ᵃˡᵍ) V] [Module.Free (ℚ_[p]ᵃˡᵍ) V]
      (hV : Module.finrank (ℚ_[p]ᵃˡᵍ) V = 2)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    -- the level is prime to `p`
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    (D : Type u) [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.NumberField.WithRigidification F D]
    (π : HeckeAlgebra (R := ℤ_[p]) D ⟨Fact.out, S, ∅, 1, by simp, hp⟩ →ₐ[ℤ_[p]] (ℚ_[p]ᵃˡᵍ))
    (ρ : GaloisRep F (ℚ_[p]ᵃˡᵍ) V) (hρ : ρ.IsAttachedAtGoodPrimes p hp S D π) :
    -- there's an integral model ρ₀ of ρ
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[p] R) (_ : IsLocalRing R) (_ : IsDomain R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R) (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R (ℚ_[p]ᵃˡᵍ)) (_ : IsScalarTower ℤ_[p] R (ℚ_[p]ᵃˡᵍ))
      (_ : ContinuousSMul R (ℚ_[p]ᵃˡᵍ))
      (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
      (_ : Module.Free R V₀) (_hV₀ : Module.rank R V₀ = 2)
      (ρ₀ : GaloisRep F R V₀)
      (r₀ : (ℚ_[p]ᵃˡᵍ) ⊗[R] V₀ ≃ₗ[ℚ_[p]ᵃˡᵍ] V),
    (ρ₀.baseChange (ℚ_[p]ᵃˡᵍ)).conj r₀ = ρ ∧
      -- such that ρ₀ is flat at all places of F dividing p
      ∀ v : HeightOneSpectrum (𝓞 F), ↑p ∈ v.asIdeal → ρ₀.IsFlatAt v :=
  sorry
