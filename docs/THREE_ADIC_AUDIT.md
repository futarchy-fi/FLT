# Three-adic audit: residual orientation and the lattice route

Checked at **2026-09-27 17:24 UTC** against FLT
`681966922f9faef8214822cbfbd8ef1ae1cf00df` and Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76` [V1]. Source checks continued
through 17:30 UTC during review. This is a source and API audit, with no
Lean edits, builds, elaboration tests or fresh transitive axiom
checks. “Body present” means source inspected. Proposed statements below are
Lean-style contracts, not declarations that have passed Lean.

The domain-coefficient route has a source-matched mathematical outline, but
still needs substantial finite-flat and arithmetic developments. The useful
residual reference is Schoof's **auxiliary-field argument**, followed by his
calculation of the extensions in the *opposite* orientation. A discriminant
bound for the original representation alone does not prove `mod_three`.
There are four small, independent algebra leaves below; none removes an
arithmetic admission.

## 1. Target and changes to the dispatch plan

The conclusion of the current `IsHardlyRamified.mod_three` is exactly [V2]:

```lean
-- Inherit the coefficient, topology, module and rank hypotheses of ModThree.lean.
∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
  ∀ (g : Field.absoluteGaloisGroup ℚ) (v : V), π (ρ g v) = π v
```

Thus the required orientation is
`0 → k(χ̄₃) → V → k → 0`. The prose in blueprint
`ch03freyreduction.tex`, theorem `hardly_ramified_mod3_reducible`, says
“extension of the cyclotomic character by the trivial representation”, which
has the opposite usual meaning. Follow the Lean functional, not that phrase.
Both that blueprint proof and `hardly_ramified_3adic_reducible` are TODOs [V3].

`three_adic` itself still has an admitted body and allows non-domain local
coefficient rings [V2]. This audit targets its hypotheses **plus `IsDomain R`**.
The model `B` supplied to the consumer in `PrimeField.lean` already has this
instance through the family statement [V4]. The lattice proof below does not
establish trace rigidity in nilpotent coefficient directions.

Two changes to `CORE_PLAN.ref.md`'s ready list are necessary:

* Both `B5Inputs.trace_eq_one_add_det_of_matrix_trivial_quotient` and
  `B5Inputs.trace_eq_one_add_det_of_trivial_quotient` have bodies in
  `FLT/GaloisRepresentation/HardlyRamified/TraceLeaves.lean`. T1, including
  the general field-valued version, should not be dispatched again [V5].
* Mathlib already has `Submodule.IsLattice`, its finite/free instances and
  rank comparison in `Mathlib/Algebra/Module/Lattice.lean`. A new definition
  of an ordinary lattice is unnecessary. Continuous stable actions and
  arithmetic preservation are separate missing work [V6, V10].

Upstream work must be considered before implementing T4a. Read-only GitHub
checks found PR [#1083](https://github.com/ImperialCollegeLondon/FLT/pull/1083)
open, last updated 2026-07-08, and
[#761](https://github.com/ImperialCollegeLondon/FLT/pull/761) open, last
updated 2026-01-12 [V11]. #1083 proposes `StableLattice.ribet_lemma`, stable
lattices, reduction and independence of residual semisimplification. Its
public declarations in `KnownIn1980s/Ribet_Lemma/Defs.lean` are admitted;
`Proofs.lean` proves separate `_proof` versions using the Slop development.
A port must connect or use those proof endpoints. Those modules are absent
from this checkout [V10]. This is a reuse candidate, not a checked dependency:
its diff was read but not built or axiom-audited. #761 still leaves base-change HR lemmas admitted
and puts isogeny preservation behind `knownin1980s` [V11]. Neither PR supplies
a verified local T2 endpoint here. This audit does not import either PR.

## 2. Primary sources and the exact input each supplies

The following PDFs were downloaded and read during this audit. Fontaine,
Raynaud and Schoof were read through extracted text; Ribet pp. 154–155 were
also rendered and visually read because the scan has no usable text layer.
The commands and URLs are in V12. Page numbers below are printed pages.

| Source | Exact location | Input and limit |
|---|---|---|
| J.-M. Fontaine, *Il n'y a pas de variété abélienne sur Z*, Invent. Math. **81** (1985), 515–538 | Théorème A, p. 515; Corollaire, p. 516; global discriminants in §3.3, Th. 3 and Cor. 3.3.2 | A finite flat group scheme killed by `pⁿ` over a local integer ring has normalized different exponent `< n + 1/(p−1)`. Use `p=3,n=1` for the auxiliary residual field. Its contribution at **2** must be calculated separately. |
| Same | Théorème B(i), p. 516; §3.4.1, Th. 4(i); proof §3.4.3 | Every finite flat 3-primary group scheme over **ℤ** is a direct sum of a constant and a diagonalizable group. This is an exact alternative for the rank-one step once unramifiedness at 2 and a global integral model are proved. It does not apply directly to a model over `ℤ[1/2]`. |
| M. Raynaud, *Schémas en groupes de type (p,…,p)*, Bull. Soc. Math. France **102** (1974), 241–280 | §2.2, Prop. 2.2.2; §3.3, Th. 3.3.3 and Cor. 3.3.6, p. 268 | Schematic closures give comparisons of finite-flat models. When the **base** absolute ramification satisfies `e < p−1`, the model is unique; generic morphisms extend and their kernels/cokernels are flat. Here the base is `ℤ₃`, so `e=1<2`, regardless of ramification in the coefficient DVR. |
| Same | Prop. 2.3.1, pp. 261–262 | A local p-divisible group whose finite levels all prolong to finite flat models prolongs uniquely. This is a possible alternative to finite-level arguments, not a theorem currently supplied by `IsFlatAt`. |
| Same | Th. 3.4.3 and Cor. 3.4.4, p. 270 | The tame inertia characters of finite-flat simple factors have fundamental-character digits in `[0,e]`. A direct small-image route needs the extra coefficient/Frobenius descent argument; this theorem alone is not the oriented global quotient. |
| K. Ribet, *A modular construction of unramified p-extensions of Q(μₚ)*, Invent. Math. **34** (1976), 151–162 | §2, Prop. (2.1), p. 154; proof pp. 154–155 | For a simple two-dimensional representation over a complete discretely valued characteristic-zero field with reducible reductions, realize a chosen ordering of the two residual characters in a **non-semisimple** reduction of a stable lattice. No finite-flat or HR preservation theorem is included. |
| R. Schoof, *Abelian varieties over Q with bad reduction in one prime only*, Compositio Math. **141** (2005), 847–868 | Def. 2.1, p. 848; example 2.4, p. 850 | Category `D` consists of finite flat p-primary groups over `ℤ[1/ℓ]` with `(σ−1)²=0` on inertia at ℓ. The Kummer group `G_ℓ` supplies the auxiliary field `ℚ(ζₚ, ℓ^(1/p))`. |
| Same | Prop. 5.1 and its proof, pp. 853–854; §6, case `ℓ=2,p=3`, p. 855 | The auxiliary-field method classifies simple objects. §6 records the class-number-one and unit calculation for `K₀=ℚ(ζ₃, ∛2)`, excluding quadratic extensions unramified outside 3. Our stronger HR bound uses Prop. 5.1's `D` setting; see the adaptation below. |
| Same | Prop. 4.1, pp. 851–852; Cor. 4.2 and its `p=3` proof, pp. 852–853 | `Ext¹_{ℤ[1/2]}(μ₃, ℤ/3ℤ)=0`: the criterion is `2 ≠ ±1 (mod 9)`. This splits extensions with **trivial subobject, cyclotomic quotient**, precisely the orientation that Ribet will force. |
| Same | Proof of Prop. 3.1, p. 850 | Sort a filtration by swapping those split adjacent factors, obtaining a diagonalizable part below an étale part. The proof then discusses abelian varieties; only its finite-group-scheme filtration argument is needed here. |

Schoof is a 2005 exposition, not a pre-1990 citation. The `ℓ=2,p=3` ingredients
used here are Fontaine/Raynaud, Kummer theory, the displayed number-field
calculation and class field theory; no modularity or abelian-variety
nonexistence theorem is being used as a substitute for the representation
argument. If a strict bibliography cutoff is required, a separate citation
task must replace Schoof's detailed exposition. Do not cite his Theorem 1.1
alone: a hardly ramified representation is not assumed to come from an
abelian variety.

## 3. Source-matched proof outline

### 3.1 Residual classification, including orientation

1. From a finite field with an algebra map `ℤ₃ → k`, prove characteristic 3;
   the present signature does not explicitly carry `[CharP k 3]` [V2].
   Regard `V` as an `𝔽₃`-module. Obtain its finite-flat model at 3 by applying
   `IsFlatAt.cond` to the open zero ideal. Glue it to the finite étale model
   over `ℤ[1/6]`, producing a finite flat model over `ℤ[1/2]`. This gluing and
   its compatibility with the `k`-action are genuine obligations. Raynaud
   Cor. 3.3.6 extends generic coefficient endomorphisms at 3.
2. The quotient at 2 is unramified. The determinant is also unramified
   there, so both inertia diagonal entries are 1. Consequently
   `(ρ(σ)−1)²=0`. The global group scheme belongs to Schoof's `D`.
   Wild inertia is pro-2; its image in this unipotent 3-group is trivial.
   Tame inertia has cyclic finite image. **Exponent 3 plus cyclicity**, not
   exponent 3 alone, gives ramification index dividing 3 for arbitrary `k`.
3. For **each simple finite-flat subquotient** `H`, form the product
   `H × G₂` of Schoof Prop. 5.1, with `G₂` his Kummer group. Both are killed
   by 3. Let `L` be its actual point field, not the projective kernel field.
   Then `K₀ = ℚ(ζ₃, ∛2) ⊆ L`, `L/ℚ` is Galois and totally complex,
   and it is unramified outside `{2,3}`. At 2, the ramification index divides
   3. At 3, Fontaine gives normalized different exponent `<3/2`. Thus

   ```text
   rd(L) < 2^(2/3) · 3^(3/2),       [K₀:ℚ] = 6.
   ```

   The existing `Odlyzko.not_discriminant_le_fontaine_bound` excludes
   `[L:ℚ] ≥ 18` [V7]. Therefore `[L:ℚ]` is **6 or 12**. This adapts
   Schoof's proof: his broader category `C` uses `rd(L)<2·3^(3/2)` and a
   degree-24 bound; the local HR condition gives the smaller constant
   already exposed by this repo. The bound must be proved for this
   **augmented** field, not imported from a statement only about `ker ρ`.
4. Since `e₂(K₀/ℚ)=3`, `L/K₀` is unramified at 2. If it has degree 2,
   it is quadratic and unramified outside 3. Schoof §6 rules this out:
   `h(K₀)=1`, there is a unique prime above 3 with residue field `𝔽₃`, and
   the unit `−1` generates its residue units. The quadratic character is
   tame at 3, so its conductor divides that prime. The ray class exact
   sequence has no quotient of order 2. This is a class-field-theory step,
   not a consequence of the absolute discriminant bound alone.
5. Thus `L=K₀`. Its Galois group is `S₃`; its normal subgroup of order 3
   acts trivially on a simple characteristic-3 module. The remaining
   `C₂`-characters are `1` and `χ̄₃`. Raynaud's uniqueness at 3 and étale
   descent away from 3 identify the simple **group schemes** as `ℤ/3ℤ`
   and `μ₃`. This works after forgetting the coefficient field, so it
   covers all finite `k`, not just `𝔽₃`. A `k`-simple factor may cease to
   be simple on restriction of scalars; take actual `𝔽₃` composition factors.
6. Apply Schoof Cor. 4.2 with `ℓ=2,p=3`. Its proof identifies the relevant
   global Kummer classes with those generated by `3` and `2`, and the
   local classes with those generated by `3` and `4`; `2` is not a cube
   in `ℚ₃`. This kills `Ext¹(μ₃,ℤ/3ℤ)`. Generic reducibility alone did
   not give this vanishing. Sorting a finite-flat composition series as
   in Prop. 3.1 gives an étale quotient above a multiplicative subobject.
7. The successive étale factors are constant `ℤ/3ℤ`. The finite action
   on their iterated extensions is a 3-group unramified outside 2.
   Schoof Prop. 3.1 uses the maximal abelian extension of `ℚ` unramified
   outside 2 to show this action is trivial. One can instead first rule
   out a quotient `C₃`: at 2 its tame abelian inertia order divides
   `2−1`, hence it is unramified everywhere, and Minkowski kills it.
   Every nontrivial finite 3-group has a quotient `C₃`. Cartier duality
   gives pure cyclotomic action on the multiplicative part.
8. Make the resulting multiplicative/étale filtration invariant under
   the coefficient endomorphisms, or descend a nonzero `𝔽₃` invariant
   functional by the finite-field trace pairing. These are explicit
   coefficient bridges, not averaging over `k/𝔽₃`. If the trivial
   quotient vanished, the whole action would be scalar `χ̄₃`, with
   determinant `χ̄₃²=1`, contrary to the determinant at complex
   conjugation. There is therefore a nonzero invariant `k`-linear
   functional; it is surjective because its target has dimension one.
   This is the exact `mod_three` conclusion.

This route avoids a separate classification of every small subgroup of
`GL₂(k)`. `Dickson.dickson_classification` is present [V10], but does not
supply the flat extension orientation. The historical direct-image plan in
`cartography/odlyzko-residual-dihedral.md` is background, not a proof of the
current endpoint [V13]. In particular, its Raynaud argument needs to track
Frobenius on the two **coefficient-field** eigencharacters: forgetting to
`𝔽₃` changes dimension to `2[k:𝔽₃]`. The auxiliary-field route avoids that
level-counting issue and its separate dihedral/torus branch.

### 3.2 Normalization and preservation for every stable lattice

Let `R` satisfy the existing three-adic hypotheses and be a domain. Put
`K=Frac(R)` and let `O` be the integral closure of `ℤ₃` in `K`. Prove that
`K/ℚ₃` is finite and `O` is its complete DVR of integers, with finite residue
field. Set `V_K=K ⊗[R] V`. Ordinary integral-closure and lattice ingredients
are available [V6]; the package identifying their topologies and continuous
Galois actions is not an existing HR theorem [V10].

First extend the original model to `O`. For an open ideal `J ⊂ O`, the
finite `R`-module `O/J` is generated by finitely many elements and is killed
by some `3ⁿ`. Hence `(O/J) ⊗[R] V` is an equivariant quotient of finitely
many copies of `V/3ⁿV`. Finite-flat products and quotients already have
bodies [V8]. This supplies scalar extension even if `R → O` is not flat;
the existing `hardlyRamified_quotient` assumes a **surjective coefficient
map** and cannot be used for normalization [V4].

For any stable `O`-lattice `Λ`, commensurability lets us rescale so that
`ϖᵃΛ₀ ⊆ Λ ⊆ Λ₀`. For every `n`,

```text
Λ / ϖ^(n+a)Λ₀  ↪  Λ₀ / ϖ^(n+a)Λ₀  ↠  its quotients,
Λ / ϖ^(n+a)Λ₀  ↠  Λ / ϖ^nΛ.
```

Thus each finite level of `Λ` is a **subquotient** of a finite-flat level
of `Λ₀`. The subgroup half needs a schematic-closure/generic-fibre lemma;
the existing quotient theorem proves the other half only [V8, V10]. Powers
of the maximal ideal are cofinal among open ideals, so this gives the
actual all-open-ideal `IsFlatAt`, not just residual flatness.

At 2, extend the original quotient to `V_K → K`. Its image on `Λ` is a
nonzero fractional ideal. Over the DVR it is principal; choose a generator
and rescale the functional to obtain `Λ → O`, surjectively, with the **same**
unramified square-trivial quotient character. Its kernel is saturated and
free of rank one. Prove continuity of the induced action and functional.
Determinant and unramifiedness away from 6 follow by the injective generic
fibre comparison. These are the four HR clauses, all needed for **every**
lattice used by Ribet.

### 3.3 Ribet and exact characters

Reduction of each such lattice satisfies `mod_three`. Its determinant
identifies the residual kernel character as `χ̄₃`, so its composition
factors are `1,χ̄₃`. These are distinct, as complex conjugation has values
`1,−1` in characteristic 3. If `V_K` were irreducible, Ribet Prop. (2.1),
with ordering **subobject `1`, quotient `χ̄₃`**, would supply a nonsplit
reduction. The invariant surjective functional furnished by `mod_three`
splits that reduction: it is nonzero on the trivial subobject, since
otherwise it factors through a nontrivial character. Normalize its value
there to get an equivariant retraction. Contradiction.

Now take a stable `K`-line in `V_K`. Its intersection with an integral
lattice is saturated, so both its lattice and the quotient are free of
rank one. Finite-flat subquotients and the unipotent inertia condition at 2
give rank-one integral characters `ψ₁,ψ₂`, flat at 3 and unramified at every
other finite prime. Their product is exactly `χ₃`.

One precise replacement for a vague appeal to “rank-one finite-flat
characters have weights 0 or 1” is Fontaine **Théorème B(i), `E=ℚ,p=3`**.
Glue every finite level of either character over ℤ. It is a sum of constant
and diagonalizable groups. Fix the character's reduction modulo `ϖ`.
Every layer of the `ϖ`-power filtration has the same residual character,
so all its `𝔽₃` factors have one type. At every level the action is
therefore wholly trivial or wholly cyclotomic, with the same choice at
all levels. Separatedness of `O` gives `ψᵢ=1` or `ψᵢ=χ₃` **exactly**.
Alternatively, reuse steps 6–7 above for pure finite levels in category
`D`, avoiding a separate formalization of all of Théorème B. The finite
levels, their pure composition factors and their coefficient action still
have to be connected; a mod-`ϖ` congruence is insufficient.

The product and complex conjugation exclude two equal choices. Triangular
linear algebra then gives `trace(ρ_K(g))=1+χ₃(g)`. Existing base-change
trace lemmas descend this equality through `R ↪ K`, and
`B5Inputs.cyclotomicCharacter_adicArithFrob` evaluates it at every prime
`q≥5` [V4, V7]. No new Chebotarev theorem is required for this step.

## 4. Missing local lemmas and their contracts

The following is the dependency list for the chosen outline, not a list
of new assumptions to insert into Lean. All identifiers introduced in this
section are **proposed**, except names explicitly listed as dependencies.
Negative API evidence is the scoped source search V10; it does not certify
that no equivalent theorem exists under another name. Sizes are estimates:
**S ≤ 2 hours** for one capped worker; M = several sessions/days; L = weeks;
XL = a substantial library or arithmetic development. Estimates overlap
where leaves share infrastructure and should not be added mechanically.

Conventions for statement sketches:

* `Γ := Field.absoluteGaloisGroup ℚ`; `χ₃`, `χ̄₃` are the cyclotomic
  characters with the algebra maps in `IsHardlyRamified.det`. `HR` means
  exactly that existing structure, with its rank equality, topology and
  coefficient instances. It is used only for rank two.
* `FF(B)` means proposed finite flat **commutative** group-scheme data over
  base `B`, or equivalent finite flat commutative Hopf-algebra data with
  geometric points. `DModel W` is such data over `ℤ[1/2]`, of 3-power
  order, an equivariant additive identification of its generic points
  with the given finite Galois module `W`, and `(σ−1)²=0` at 2.
  `Simple G` means nonzero, with no proper nonzero closed finite-flat subgroup.
  These records must contain models and maps, not the desired classification.
* `PointField G` is the fixed field of the kernel of the action on all
  geometric points. `K₀` is the splitting field of `X³−2` over ℚ.
  `UnramifiedOutside S L/K` and `e_q(L/K)` mean unramifiedness at all
  finite primes off `S` and actual ramification indices, respectively.
* `ExtOf W a b` means a stable line with action `a` and quotient action
  `b`; `SplitExtOf` additionally supplies a stable complement. This is
  the orientation of the proposed API in upstream #1083 [V11].
* In the lattice rows, `O` is the complete DVR above, `K` its fraction
  field, `k=O/𝔪`, `ϖ` a uniformizer and `W` has `K`-dimension two.
  `Stable ρ Λ` means `ρ(g)Λ=Λ` for every `g`, with
  `[Submodule.IsLattice K Λ]`. `ρΛ` and `ρ̄Λ` must be constructed
  continuous representations; the notation does not assume their HR.
* `Flat3 ψ` for a rank-one integral character means every open-ideal
  coefficient quotient has `GaloisRep.HasFlatProlongationAt` at 3.
  `Pure W a` abbreviates the explicit assertion `∀ g x, g • x = a(g) • x`.

### Residual arithmetic and finite-flat models

**R0. Recover characteristic and coefficient action. M.**

```lean
theorem charP_three_of_finite_padic_algebra
    [Field k] [Finite k] [Algebra ℤ_[3] k] : CharP k 3
-- In addition: the algebra action of k on generic points extends to the model at 3.
```

Dependencies: `PadicInt.isUnit_iff` and the residue homomorphism in
Mathlib `NumberTheory/Padics/{PadicIntegers,RingHoms}.lean`; finite-field
characteristic APIs; for extending the action, Raynaud Cor. 3.3.6 and R1.
The action extension is part of model construction, not an extra algebraic
axiom. Do not strengthen `mod_three`'s signature by simply assuming char 3.

**R1. Global model from local flatness and unramifiedness. L.**

```lean
theorem global_model_away_two (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {2, 3} W) : Nonempty (ModelOverZInvTwo W)
theorem global_model_over_int (W : FiniteContinuousGaloisModule)
    (h3 : HasFiniteFlatModel ℤ_[3] W.localAtThree)
    (hur : UnramifiedOutside {3} W) : Nonempty (ModelOverInt W)
```

These proposed model records include an equivariant generic-points
isomorphism and functoriality for coefficient maps. Construct the étale
Hopf order away from 3, intersect/glue with the local flat order, and prove
finiteness, flatness and generic-fibre comparison. Dependencies:
`GaloisModule.IsFiniteFlat`, `GaloisModule.GenericFiber` in
`FLT/GroupScheme/FiniteFlat.lean`, and Raynaud Cor. 3.3.6 for extending
morphisms. Schoof §4's Mayer–Vietoris setup describes this local/global
interface; this particular representation-to-model theorem is a derived
obligation. `FLT/MazurChapter/AdmissibleGroupSchemes.lean` has admitted
constant/multiplicative objects and is not a ready implementation [V8, V9].

**R2. Nilpotent inertia calculation. S, ready now.**

```lean
theorem cube_eq_one_of_sub_one_sq_eq_zero
    {A : Type*} [Ring A] [CharP A 3] (u : A)
    (hu : (u - 1)^2 = 0) : u^3 = 1
```

Dependencies: `add_pow_char_of_commute` in Mathlib
`Algebra/CharP/Lemmas.lean`, `Commute.one_left`, power identities [V14].
Apply it to `1+(u−1)` and use `(u−1)³=0`. This proves element orders
divide 3; it does **not** prove that a whole inertia image has order ≤3.

**R3. From HR at 2 to the tame ramification index. L.**

```lean
theorem inertia_two_sq_zero (hρ : HR ρ̄) :
    ∀ σ ∈ inertiaTwo, (ρ̄.localAtTwo σ - 1)^2 = 0
theorem ramification_two_dvd_three
    (hD : DModel W) (hkill : ∀ x : W, (3 : ℕ) • x = 0) :
    e_two (PointField W / ℚ) ∣ 3
```

Dependencies: the quotient and determinant in `HardlyRamified/Defs.lean`,
rank-two linear algebra, R2, pro-2 wild inertia and cyclic tame inertia,
plus the point-field/completion comparison. Relevant existing files are
Mathlib `NumberTheory/RamificationInertia/{Inertia,Galois,Ramification}.lean`
and `RingTheory/Valuation/RamificationGroup.lean`; they do not by themselves
provide this endpoint [V10]. Source: Schoof Prop. 5.1, proof on p. 854.

**R4. Kummer auxiliary object and its point field. L.**

```lean
theorem exists_kummer_two_model :
    ∃ G₂ : FF (ℤ[1/2]), KilledBy 3 G₂ ∧ InCategoryD G₂ ∧
      Nonempty (PointField G₂ ≃ₐ[ℚ] K₀)
theorem augmented_field_data (H : FF (ℤ[1/2]))
    (hs : Simple H) (hD : InCategoryD H) :
    ∃ L, IsPointField (H.prod G₂) L ∧ Nonempty (K₀ →ₐ[ℚ] L) ∧
      IsTotallyComplex L ∧ UnramifiedOutside {2, 3} (L / ℚ) ∧ e_two (L / ℚ) ∣ 3
```

Dependencies: R1/R3, finite-flat products, Kummer finite étale algebras,
Mathlib `FieldTheory/SplittingField/Construction.lean`, and
`GaloisRepresentation.Chebotarev.exists_finiteGalois_realization` in
`HardlyRamified/Chebotarev/FiniteGaloisRealization.lean` [V7, V8]. The latter
realizes a supplied finite quotient; it does not prove its ramification.
Source: Schoof example 2.4 and Prop. 5.1. Include the proof that a simple
3-primary finite-flat object is killed by 3.

**R5. Fontaine bound and local/global different conversion. XL.**

```lean
theorem augmented_discriminant_bound
    (hL : IsPointField (H.prod G₂) L) (hs : Simple H) (hD : InCategoryD H) :
    |(NumberField.discr L : ℝ)| ≤
      ((2 : ℝ)^(2/3 : ℝ) * (3 : ℝ)^(3/2 : ℝ)) ^ Module.finrank ℚ L
```

Dependencies: R3/R4, Fontaine Théorème A and its corollary, different in
towers and the discriminant product formula. Mathlib ramification files
above and `NumberTheory/NumberField/Discriminant/Defs.lean` are foundations;
the Fontaine estimate was not located [V10]. It is enough to weaken the
paper's strict bound to this non-strict one. Do not apply `n=1` to an
arbitrary `3ⁿ`-torsion field or to an unrestricted tower.

**R6. Arithmetic of the sextic auxiliary field. L.**

```lean
theorem kummer_two_field_data :
    Module.finrank ℚ K₀ = 6 ∧ NumberField.classNumber K₀ = 1 ∧
    UniquePrimeAbove 3 K₀ ∧ ResidueFieldAtThreeIsF3 K₀ ∧
    ResidueUnitsGeneratedByNegOne K₀ ∧ e_two (K₀ / ℚ) = 3
```

The last three predicates mean a specified prime with residue-field
isomorphism to `ZMod 3`, and surjectivity of the reduction of the subgroup
of units generated by `−1`. Dependencies: explicit integral basis/prime
decomposition of `X³−2`'s splitting field; Mathlib
`NumberTheory/NumberField/ClassNumber.lean` and
`NumberTheory/NumberField/Discriminant/Basic.lean` [V15]. Source: Schoof
§6, case `ℓ=2,p=3`. The paper states the class number; this audit has not
run a computer-algebra certificate. A proof/certificate in Lean is missing;
this is not the class-number-one theorem for the quadratic field `ℚ(ζ₃)`.

**R7. Exclude the quadratic extension. L, with an XL CFT dependency if
implemented through general reciprocity.**

```lean
theorem no_quadratic_extension_auxiliary
    [NumberField L] [Algebra K₀ L] [FiniteDimensional K₀ L]
    (hur : UnramifiedOutside {primesAboveThree} (L / K₀)) :
    Module.finrank K₀ L ≠ 2
```

Dependencies: R6; tame quadratic conductor bound at residue characteristic
3; the ray-class exact sequence and the quadratic case of Artin
reciprocity. No ray-class endpoint was located in the searched Lean sources
[V10]. Source: Schoof §6, p. 855. A direct Kummer/unit computation is an
alternative research task, not a free replacement: it must classify all
square classes and verify their local ramification. A polynomial
discriminant divisible by 2 alone does not prove field ramification.

**R8. Numerical degree reduction. S, ready now, conditional on its
explicit discriminant input.**

```lean
theorem auxiliary_degree_eq_six_or_twelve
    (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyComplex L]
    (h6 : 6 ∣ Module.finrank ℚ L)
    (hdisc : |(NumberField.discr L : ℝ)| ≤
      ((2 : ℝ)^(2/3 : ℝ) * (3 : ℝ)^(3/2 : ℝ)) ^ Module.finrank ℚ L) :
    Module.finrank ℚ L = 6 ∨ Module.finrank ℚ L = 12
```

Dependencies: `Odlyzko.not_discriminant_le_fontaine_bound` in
`FLT/Odlyzko.lean`, `Module.finrank_pos`, divisibility arithmetic [V7].
Derive degree `<18`; it is positive and divisible by 6. Connecting `h6`
to the actual inclusion of `K₀` belongs to R4/R6, not this cap. The
wrapper's dependencies must receive a fresh axiom check when implemented.

**R9. Classification of simple objects. L after R4–R8.**

```lean
theorem simple_D_three (G : FF (ℤ[1/2])) (hs : Simple G)
    (hD : InCategoryD G) :
    Nonempty (G ≅ constantThree) ∨ Nonempty (G ≅ muThree)
```

Dependencies: R4–R8, `S₃`'s normal 3-subgroup and fixed vectors of finite
p-groups in characteristic p, plus Raynaud Cor. 3.3.6/model uniqueness.
The degree-12 branch is killed by R7, not by a group order assertion.
Source: Schoof Prop. 5.1 and the adapted §6 argument. Mathlib finite
group/representation theory and the existing finite-Galois realization
are foundations; Dickson is optional, not a dependency of this route.

**R10. Split the reverse extension. XL (p=3 specialization may reduce
scope, but is not S).**

```lean
theorem split_extension_mu_three_by_constant_three
    (E : ShortExactFiniteFlatSequence (ℤ[1/2]) constantThree muThree) :
    Nonempty E.Splitting
```

Here the sequence is explicitly `0 → constantThree → E.middle → muThree
→ 0`. Dependencies: connected–étale splitting over `ℤ₃`, local/global
gluing R1, Kummer theory, units/classes in `ℚ(ζ₃)` and their maps to
`ℚ₃(ζ₃)`. Source: Schoof Prop. 4.1, Cor. 4.2, p=3 proof. A mod-9
calculation is the last step, not the whole Ext calculation. The
`AdmissibleGroupSchemes.lean` scaffold does not supply these inputs [V9].

**R11. Pure étale and multiplicative finite levels. L.**

```lean
theorem D_etale_three_constant (G : FF (ℤ[1/2]))
    (hD : InCategoryD G) (hf : HasFiltration G constantThree) :
    Pure G.geometricPoints 1
theorem D_multiplicative_three_cyclotomic (G : FF (ℤ[1/2]))
    (hD : InCategoryD G) (hf : HasFiltration G muThree) :
    Pure G.geometricPoints χ₃
```

Dependencies: finite 3-group quotient of order 3, local tame Frobenius
conjugation at 2, R1, Cartier duality, and
`NumberField.InertiaComparison.intermediateField_eq_bot_of_localInertia`
in `FLT/FreyCurve/Serre/UnramifiedCharacter.lean` [V7]. Its
`GaloisRep.trivial_of_everywhere_unramified` is specialized to `ZMod p`;
the intermediate-field theorem is the more general reusable ingredient.
Sources: Schoof Prop. 3.1 proof; Fontaine §3.4.3 steps 1–2.

**R12. Functorial sorted filtration. L.**

```lean
theorem D_three_sorted_filtration (G : FF (ℤ[1/2])) (hD : InCategoryD G) :
    ∃ E : ShortExactFiniteFlatSequenceWithMiddle G,
      HasFiltration E.left muThree ∧ HasFiltration E.right constantThree ∧
      PreservedByAllEndomorphisms E
```

Dependencies: R9/R10, finite-flat subobjects/quotients, induction on
3-power order and the Hom vanishing between distinct generic characters
for functoriality; R11 identifies the resulting actions. Source: sorting
argument in Schoof Prop. 3.1. The functoriality assertion is additional
derived bookkeeping needed for coefficient actions, not a quotation of
the proposition's abelian-variety conclusion.

**R13. Coefficient-field quotient and exact `mod_three`. M after the
arithmetic, not ready now.**

```lean
theorem trivial_quotient_over_coefficients
    (hρ : HR ρ̄) (hmodel : DModel (ρ̄.restrictScalars (ZMod 3)))
    (hsorted : SortedFiltrationWithPureActions hmodel) :
    ∃ π : V →ₗ[k] k, Function.Surjective π ∧ ∀ g v, π (ρ̄ g v) = π v
```

`SortedFiltrationWithPureActions` is the exact sequence of R12 together
with R11's two pointwise action equalities. Dependencies: R0/R1/R12,
complex conjugation's cyclotomic value, dimension two, determinant;
alternatively the nondegenerate finite-field trace pairing in Mathlib
`FieldTheory/Finite/Trace.lean` and `RingTheory/Trace/Basic.lean` [V15].
No assumption `[k = ZMod 3]` and no division by `[k:𝔽₃]` is permitted.
Applying this after constructing its inputs closes the residual endpoint.

### Integral lattices and the characteristic-zero obstruction

**L0. Normalize the coefficient order. L.**

```lean
theorem normalization_padic_order
    (R : Type*) [CommRing R] [IsDomain R] [Algebra ℤ_[3] R]
    [Module.Finite ℤ_[3] R] [Module.Free ℤ_[3] R] :
    FiniteDimensional ℚ_[3] (FractionRing R) ∧
      IsCompleteDVRModel (integralClosure ℤ_[3] (FractionRing R)) (FractionRing R)
```

The first factor presupposes construction of the induced `ℚ₃` algebra.
The proposed second package includes a finite free `ℤ₃`-module, finite
residue field of characteristic 3, fraction-field identification, DVR,
adic completeness, module topology, and continuous maps from `R` and to
`K`. Dependencies: Mathlib `RingTheory/DedekindDomain/IntegralClosure.lean`
(`IsIntegralClosure.finite`, `.module_free`, `.rank`, `.isDedekindDomain`),
`NumberTheory/LocalField/Basic.lean`, `NumberTheory/Padics/LocalField.lean`
and valuation/completion APIs [V6]. Establish localness/completeness;
being an integral closure in a field alone is not the complete DVR proof.

**L1. Continuous representation of a stable lattice and its reduction. M–L.**

```lean
def latticeGaloisRep (ρ : GaloisRep ℚ K W) (Λ : Submodule O W)
    [Submodule.IsLattice K Λ] (hΛ : Stable ρ Λ) : GaloisRep ℚ O Λ
theorem lattice_generic_equiv (hΛ : Stable ρ Λ) :
    ∃ e : K ⊗[O] Λ ≃ₗ[K] W, (ρΛ.baseChange K).conj e = ρ
```

Also construct `ρ̄Λ`, its finite/discrete residue coefficients and rank
two. Dependencies: `Submodule.IsLattice.{finite,free,rank'}` and
`Module.Basis.extendOfIsLattice` in Mathlib `Algebra/Module/Lattice.lean`;
`GaloisRep.baseChange`, `.conj` in
`FLT/Deformations/RepresentationTheory/GaloisRep.lean` [V6, V4].
#1083's algebraic `latticeRep`/`reducedRep` are reuse candidates; continuity
in the repo's `GaloisRep` topology still needs verification [V11].

**L2. Flatness under finite coefficient extension. L.**

```lean
theorem flat_three_normalization (hflat : ρ.IsFlatAt v₃) :
    (ρ.baseChange O).IsFlatAt v₃
```

Inherit L0's finiteness/topology and the original finite free module.
Dependencies: finite generation and open-ideal/power cofinality, tensor
quotient maps, `GaloisModule.IsFiniteFlat.finPow` and `.quotient` in
`FLT/GroupScheme/FiniteFlat.lean` [V8]. Construct the surjection from a
finite power of `V/3ⁿV` described in §3.2, including equivariance. Source:
derived finite-flat product/quotient argument. This is not
`B5Inputs.flatAt_quotient`, whose coefficient map is surjective [V4].

**L3. Finite-flat subgroup closure with points comparison. L.**

```lean
theorem GaloisModule.IsFiniteFlat.subobject
    (hX : GaloisModule.IsFiniteFlat A F Fbar X)
    (i : Y →+[Fbar ≃ₐ[F] Fbar] X) (hi : Function.Injective i) :
    GaloisModule.IsFiniteFlat A F Fbar Y
```

Inherit the Dedekind/fraction-field/separable-closure and finite-continuous
action hypotheses of the existing `.quotient`; use `A=ℤ₃` here.
Dependencies: schematic closure of the generic subgroup, Hopf ideal
quotient, flatness of its coordinate ring, generic points identification.
`HopfAlgebra.IsFiniteFlat.quotient` and the generic-fibre machinery in
`FLT/GroupScheme/FiniteFlat.lean` are starting points [V8]. No public
Galois-module subgroup theorem was located by V10. Source: the closure
construction used in Raynaud §2.2; Cor. 3.3.6 is another route over `ℤ₃`.

**L4. Flatness for every commensurate lattice. M after L1–L3.**

```lean
theorem flat_three_of_stable_lattice
    (hflat : ρΛ₀.IsFlatAt v₃) (hΛ : Stable ρK Λ) : ρΛ.IsFlatAt v₃
```

Dependencies: commensurability, the two finite-level maps in §3.2,
L3 and existing finite-flat quotients, and cofinality of `ϖⁿ` among open
ideals. Mathlib lattices are the starting point; #1083 proposes
`Submodule.IsLattice.exists_smul_le` [V6, V11]. Acceptance quantifies
over **all** open coefficient ideals.

**L5. Saturated quotient at 2 for any lattice. M–L.**

```lean
theorem tame_two_of_stable_lattice
    (hπ : HasUnramifiedQuadraticQuotientAtTwo ρΛ₀)
    (hΛ : Stable ρK Λ) : HasUnramifiedQuadraticQuotientAtTwo ρΛ
```

The proposed predicate is exactly the `isTameAtTwo` field of
`IsHardlyRamified`, with the same local Galois group and inertia subgroup.
Dependencies: L1; principal fractional ideals of a DVR; image of the
generic functional, rank-one free saturated kernel, and continuity.
The general source is lattice algebra; neither Ribet Prop. 2.1 nor the
Frey-specific `torsion_quotient_at_two` in
`HardlyRamified/AtTwo.lean` proves this transport statement [V16].

**L6. Assemble HR transport. M after L0–L5.**

```lean
theorem hardlyRamified_of_stable_lattice
    (hρ : HR ρ) (hΛ : Stable (ρ.baseChange K) Λ) : HR ρΛ
```

Dependencies: L0–L5, determinant under scalar extension/conjugation and
injectivity of `O → K` to descend inertia equalities. Supply rank and
topology instances, as in L1. Existing coefficient-quotient preservation
is useful for `ρ̄Λ` after this theorem, not for proving it [V4].

**Q0. Residual composition factors, with distinctness. M.**

```lean
theorem residual_characters (hρ : HR ρΛ) :
    ExtOf ρ̄Λ χ̄₃ 1 ∧ χ̄₃ ≠ 1
```

Dependencies: R13 (the proved residual classification), maximal-ideal
quotient preservation, determinant on a stable line/quotient, and the
cyclotomic value at complex conjugation. `IsHardlyRamified.det` gives
the determinant but does not itself build the kernel representation
[V2, V4]. The rank-one trace lemmas are already present [V5].

**Q1. Ribet's lemma. L if developed locally; price a port only after
checking #1083.**

```lean
theorem ribet_opposite_lattice (hirr : ρK.IsIrreducible)
    (h₀ : Stable ρK Λ₀) (hss : ResidualFactors ρ̄Λ₀ 1 χ̄₃) :
    ∃ Λ, Stable ρK Λ ∧ ExtOf ρ̄Λ 1 χ̄₃ ∧ ¬ SplitExtOf ρ̄Λ 1 χ̄₃
```

Dependencies: complete DVR, dimension two, L1; residual
semisimplification independence, or all-lattice input from L6/Q0. Exact
source: Ribet §2, Prop. 2.1. Upstream #1083's
`StableLattice.ribet_lemma_proof` in
`FLT/KnownIn1980s/Ribet_Lemma/Proofs.lean`, backed by `ribet_lemma_slop`,
is the concrete reuse target [V11]. The unsuffixed public declaration
remains admitted in that diff. A port must audit the proof endpoint's
transitive dependencies. A new proof must retain the nonsplitting conclusion.

**Q2. An invariant functional splits the opposite extension. S, ready now.**

```lean
theorem equivariant_retraction_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (i : k →ₗ[k] V) (q : V →ₗ[k] k)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : LinearMap.range i = LinearMap.ker q)
    (hiG : ∀ g x, ρ g (i x) = i x)
    (hqG : ∀ g v, q (ρ g v) = (χ g : k) * q v)
    (hne : ∃ g, χ g ≠ 1)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    ∃ r : V →ₗ[k] k, r.comp i = LinearMap.id ∧ ∀ g v, r (ρ g v) = r v
```

Dependencies: `Submodule.liftQ` in Mathlib
`LinearAlgebra/Quotient/Basic.lean`, `LinearMap.quotKerEquivRange` in
`LinearAlgebra/Isomorphisms.lean`, and elementary linear algebra [V14].
If `π ∘ i=0`, factor through `q`; a nonzero map `k→k` would intertwine
`χ` and `1`, contradicting `hne`. Otherwise rescale `π` by `π(i 1)⁻¹`.
This is pure algebra and uses neither HR nor `mod_three`.
The kernel of `r` is the stable complement needed to contradict Q1.

**Q3. Generic reducibility from all lattices. M after dependencies.**

```lean
theorem not_irreducible_of_all_lattices_trivial_quotient
    (h₀ : Stable ρK Λ₀)
    (hQ : ∀ Λ, Stable ρK Λ → HasTrivialQuotient ρ̄Λ)
    (hss : ResidualFactors ρ̄Λ₀ 1 χ̄₃) (hne : χ̄₃ ≠ 1) :
    ¬ ρK.IsIrreducible
```

Dependencies: Q1/Q2 and the line/functional descriptions of extensions.
L6/R13/Q0 discharge its arithmetic hypotheses. Keep them explicit in a
conditional assembly lemma; its completion alone is not T4a completed.

### Exact rank-one characters and the final trace

**C0. Integral rank-one subquotients of a reducible generic fibre. M–L.**

```lean
theorem integral_characters_of_reducible (hρ : HR ρΛ)
    (hred : ¬ ρK.IsIrreducible) :
    ∃ ψ₁ ψ₂ : Γ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Flat3 ψ₁ ∧ Flat3 ψ₂ ∧
      UnramifiedOutside {3} ψ₁ ∧ UnramifiedOutside {3} ψ₂ ∧
      GenericExtensionOf ρK ψ₁ ψ₂ ∧ ψ₁ * ψ₂ = χ₃
```

Dependencies: stable proper subspace from reducibility, its saturated
intersection with `Λ`, finite-flat subquotients L3/L4, and the HR inertia
calculation. In characteristic zero a rank-one subquotient of a unipotent
operator has eigenvalue 1, proving unramifiedness at 2. Module freeness is
over `O`, not over the original possibly nonnormal `R`.

**C1. Rank-one finite levels have pure action. L after the residual and
finite-flat work; XL if importing Fontaine B independently.**

```lean
theorem rank_one_pure_levels (ψ : Γ →* Oˣ) (hc : Continuous ψ)
    (hf : Flat3 ψ) (hur : UnramifiedOutside {3} ψ) :
    (∀ n g, reduceMod (𝔪^n) (ψ g : O) = 1) ∨
    (∀ n g, reduceMod (𝔪^n) (ψ g : O) = reduceMod (𝔪^n) (χ₃ g : O))
```

Dependencies: R1 at base ℤ, Fontaine Théorème B(i) for `p=3`, and the
coefficient-stable filtration by `ϖ` powers. Alternatively use R9/R11/R12
over `ℤ[1/2]`. Prove the residual rank-one action is `1` or `χ̄₃` by the
same simple-factor/coefficient descent as R13; every `ϖ`-adic layer has
that same type. The disjunction is **outside** `∀ n`: the choice cannot
change with `n`. This supplies higher congruences rather than assuming
them. Raynaud Prop. 2.3.1 plus p-divisible-group classification is an
alternative development, not an existing API shortcut [V10].

**C2. Separatedness and exact trace descent. M after C0/C1.**

```lean
theorem rank_one_eq_one_or_cyclotomic (ψ : Γ →* Oˣ)
    (hc : Continuous ψ) (hf : Flat3 ψ) (hur : UnramifiedOutside {3} ψ) :
    ψ = 1 ∨ ψ = χ₃
theorem domain_trace (hρ : HR ρ) [IsDomain R] :
    ∀ g, LinearMap.trace R V (ρ g) = 1 + algebraMap ℤ_[3] R (χ₃ g)
```

Dependencies: C1 and `IsHausdorff.eq_iff_smodEq`; C0, exact determinant,
complex conjugation, triangular trace calculation, and
`B5Inputs.trace_baseChange_conj`/`padic_domain_map_injective` in
`HardlyRamified/B5Inputs.lean` [V4, V14]. `χ₃` in the last formula is
the `ℤ₃`-valued character of `Defs.lean`, coerced from units. The
Frobenius specialization uses the already-present
`B5Inputs.cyclotomicCharacter_adicArithFrob` in
`HardlyRamified/Chebotarev/FrobeniusTraces.lean` [V7]. Reuse the trace
API and prove only missing assembly; do not redispatch T1.

**C3. Equality from all ideal-power quotients. S, ready now; useful for
C2 as well as optional T5.**

```lean
theorem eq_of_all_power_quotients {R : Type*} [CommRing R]
    (I : Ideal R) [IsHausdorff I R] {x y : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I^n) x = Ideal.Quotient.mk (I^n) y) :
    x = y
```

Dependencies: `Ideal.Quotient.mk_eq_mk_iff_sub_mem` in Mathlib
`RingTheory/Ideal/Quotient/Defs.lean`, `IsHausdorff.eq_iff_smodEq` in
`RingTheory/AdicCompletion/Basic.lean` [V14]. Unlike an all-ring trace
claim, this wrapper is unconditional elementary algebra. It does not
produce the power-quotient equalities.

## 5. Capped dispatch order

| Order | Leaf | Cap | Reviewable output |
|---|---|---|---|
| 1 | R8: auxiliary degree is 6 or 12 | ≤1 h | A conditional lemma with the displayed discriminant bound and divisibility assumptions; no Fontaine assumption concealed in a definition. |
| 2 | R2: square-zero unipotent has cube 1 | ≤1 h | The noncommutative ring statement above; do not enlarge the task to tame inertia. |
| 3 | Q2: invariant functional gives a retraction | ≤2 h | The explicit linear-algebra statement, with a stable-complement corollary if it fits the cap. No residual classification assumption. |
| 4 | C3: equality from all power quotients | ≤1 h | A separatedness wrapper; use it for the finite-level character route. |

All four have only source-present dependencies [V7, V14]. Fresh targeted
builds and `#print axioms` are acceptance work for their implementers;
they were intentionally not run in this docs-only audit. “S” estimates
proof work against those APIs, not a guarantee that all transitive
dependencies are admission-free. Do not count a conditional wrapper as
proving its missing arithmetic hypotheses.

The next research/implementation package after those leaves should be
**L3 plus its generic-points comparison**, or a bounded review/port of
upstream #1083. Neither is priced S. The critical residual chain is
R1/R3/R4 → R5–R8 → R9/R10 → R11/R12 → R13. The lattice chain is
L0–L6 → Q0/Q1/Q2 → Q3 → C0/C1/C2. There is no two-hour route to
`three_adic` in this inventory.

## 6. Reproducible evidence ledger

Run from this worktree. V1–V16 were
read-only checks except the scratch downloads/rendering in V12. A source
search is evidence about the inspected snapshot, not a permanent status.

**V1.** `git rev-parse HEAD`; `git -C .lake/packages/mathlib rev-parse HEAD`; `date -u '+%Y-%m-%d %H:%M UTC'`

Evidence: Revisions and timestamp in the header.

**V2.** `cat FLT/GaloisRepresentation/HardlyRamified/{Threeadic,ModThree,Defs}.lean`

Evidence: Exact signatures, admitted two endpoints, and four HR fields.

**V3.** `sed -n '210,252p' blueprint/src/chapter/ch03freyreduction.tex`; `sed -n '105,125p' blueprint/src/chapter/ch04overview.tex`

Evidence: Opposite wording in residual prose; omitted proofs and the sketch of the lattice route.

**V4.** `cat FLT/GaloisRepresentation/HardlyRamified/{B5Inputs,Family,PrimeField}.lean`; `sed -n '375,425p' FLT/Deformations/RepresentationTheory/GaloisRep.lean`

Evidence: Surjective quotient preservation, trace transport, domain family model, caller, and all-open-ideal flatness definition.

**V5.** `cat FLT/GaloisRepresentation/HardlyRamified/TraceLeaves.lean`

Evidence: Both T1 statements have proof bodies.

**V6.** `cat .lake/packages/mathlib/Mathlib/Algebra/Module/Lattice.lean`; `rg -n 'theorem|lemma' .lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`

Evidence: Existing lattice class, free/rank API and integral-closure finiteness/Dedekind API.

**V7.** `cat FLT/Odlyzko.lean`; `cat FLT/GaloisRepresentation/HardlyRamified/Chebotarev/FiniteGaloisRealization.lean`; `cat FLT/FreyCurve/Serre/UnramifiedCharacter.lean`; `rg -n 'cyclotomicCharacter_adicArithFrob' FLT/GaloisRepresentation/HardlyRamified/Chebotarev/FrobeniusTraces.lean`

Evidence: Existing numerical contradiction, finite quotient realization, Minkowski bridge and Frobenius evaluation.

**V8.** `rg -n 'IsFiniteFlat|lemma|theorem' FLT/GroupScheme/FiniteFlat.lean`; `cat FLT/Deformations/RepresentationTheory/Flat.lean`

Evidence: Products, finite powers, isomorphism transport and quotients; these do not constitute the subgroup/lattice theorem.

**V9.** `rg -n 'def |theorem|sorry|axiom' FLT/MazurChapter/AdmissibleGroupSchemes.lean`

Evidence: The admitted objects and results listed above.

**V10.** `rg -n -i 'ribet|stableLattice|stable_lattice|fontaine|RayClass|IsFiniteFlat.*subobject|IsFiniteFlat.*subgroup|hardlyRamified_of_stable_lattice|rank_one_pure_levels|eq_of_all_power_quotients' FLT .lake/packages/mathlib/Mathlib --glob '*.lean'`; `cat FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean`; `rg --files .lake/packages/mathlib/Mathlib`

Evidence: Scoped missing-endpoint search, existing Dickson statement and available file paths. Mentions of Fontaine/numerical bounds are not the missing finite-flat theorem.

**V11.** `gh pr view 1083 --repo ImperialCollegeLondon/FLT --json state,title,updatedAt,files,url`; same for `761`; `gh pr diff 1083 --repo ImperialCollegeLondon/FLT`; same for `761`

Evidence: Both open; admitted public declarations plus separate `_proof` endpoints in #1083, remaining admissions in #761.

**V12.** Python `requests.get(url, timeout=35)` for the URLs below, then `pypdf.PdfReader(path).pages[i].extract_text()`; `gs -q -dSAFER -dBATCH -dNOPAUSE -sDEVICE=png16m -r120 -dFirstPage=5 -dLastPage=6 -sOutputFile=/tmp/three-adic-audit/ribet-%d.png /tmp/three-adic-audit/ribet.pdf`

Evidence: Primary source sections above read; Ribet PDF pages 5–6 are printed pp. 154–155. Scratch files are outside the commit.

**V13.** `cat cartography/odlyzko-residual-dihedral.md`; `sed -n '1,210p' cartography/odlyzko-r1.md`; `sed -n '100,140p' cartography/r-eq-t-reconciled.md`

Evidence: Earlier direct-image argument and upstream overlap, treated as historical leads and rechecked against sources.

**V14.** `sed -n '130,155p' .lake/packages/mathlib/Mathlib/Algebra/CharP/Lemmas.lean`; `rg -n 'liftQ|quotKerEquivRange' .lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`; `rg -n 'mk_eq_mk_iff_sub_mem' .lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean`; `sed -n '40,80p' .lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean`

The quotient-isomorphism declaration is located by
`rg -n 'quotKerEquivRange' .lake/packages/mathlib/Mathlib/LinearAlgebra/Isomorphisms.lean`.

Evidence: Elementary dependencies of R2/Q2/V3.

**V15.** `rg -n 'traceForm_nondegenerate' .lake/packages/mathlib/Mathlib/{FieldTheory/Finite/Trace,RingTheory/Trace/Basic}.lean`; `rg --files .lake/packages/mathlib/Mathlib/NumberTheory/NumberField`

Evidence: Trace-pairing reference and number-field API paths; no sextic-field computation asserted.

**V16.** `cat FLT/GaloisRepresentation/HardlyRamified/AtTwo.lean`

Evidence: The Frey-specific quotient and its hypotheses, not stable-lattice transport.

Primary-source URLs for V12:

* Fontaine: <https://www.imo.universite-paris-saclay.fr/~fontaine/varabZ.pdf>
* Raynaud: <https://www.numdam.org/item/BSMF_1974__102__241_0.pdf>
* Ribet: <https://math.berkeley.edu/~ribet/Articles/invent_34.pdf>
* Schoof: <https://reneschoof.github.io/abvar1prime.pdf>
* Schoof's errata: <https://reneschoof.github.io/ssnewerrata.txt>. The posted
  correction concerns the proof of Prop. 4.1's Herbrand/Spiegelungsatz
  citation. The `p=3` specialization can use the explicit class-number-one
  calculation for `ℚ(ζ₃)` instead; it should not import an uncorrected
  general Herbrand argument.

The briefing's read-only `CORE_PLAN.ref.md` was read at sections T and the
dispatch notes (`sed -n '250,435p'` and `sed -n '1080,1115p'`). It is not
part of this commit. The audit's mathematical dependencies remain open;
the deliverable is this source-matched outline and dispatch inventory.
