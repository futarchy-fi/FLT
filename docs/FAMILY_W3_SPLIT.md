# FAMILY-W3 — prerequisites for the two potential-modularity gates

Scope: the two gaps in `FAMILY_GOAL_LEDGER.md`, not GL* lifts or three-adic
sorting. Baseline `7a4bca25`; checked 2026-09-30 with the `rg` commands below.
F1–F3 are present. Snowden [S, §3 (A1), Thm. 5.1.2] requires **residual**
absolute irreducibility on the cyclotomic kernel, as well as weight two for
the characteristic-zero lift. Neither follows from the present global
absolute-irreducibility theorem by restriction alone.

W1–W5 are implemented in the modules below. W4 now proves the unconditional
quadratic self-twist theorem. The arithmetic restriction and weight-two
bridges still require the downstream results listed below.

Sources: [S] Snowden, arXiv:0905.4266v1, §1.2, §3 and Thm. 5.1.2;
[R] Raynaud, *Schémas en groupes de type (p,...,p)*, BSMF 102 (1974),
Thm. 3.3.3 / Cor. 3.3.6 (the finite-flat model gate in the parent ledger);
[T] Tate, *p-divisible groups*, Proc. Conf. Local Fields (1967), §2
(the exact sequences required of torsion levels);
[C] Clifford, *Representations induced in an invariant subgroup*,
Ann. Math. 38 (1937), restriction to a normal subgroup.
Only [S]'s text is cached in `Scratch/snowden.txt`; [R]/[T]/[C] identify
source obligations, not a verified ready-to-import theorem in Lean.

## W1 — IMPLEMENTED: coefficient torsion-level exactness (cap 220 lines)

New `FLT/Deformations/RepresentationTheory/PrimePowerExact.lean`.
Generic coefficient algebra for the torsion tower in [T, §2]. For a domain
R and a nonzero a, multiplication by a^n embeds R/(a^m) into R/(a^(m+n));
reduction onto R/(a^n) has precisely that image as kernel. Use explicit
linear maps, not an existence hypothesis for an exact sequence.

Namespace `GaloisRepresentation.PrimePower`; binders:
```lean
variable {R : Type*} [CommRing R]
abbrev Quot (a : R) (n : ℕ) := R ⧸ Ideal.span {a ^ n}
-- inclusion multiplies representatives by a^n; reduction keeps representatives.
def inclusion (a : R) (m n : ℕ) : Quot a m →ₗ[R] Quot a (m+n)
def reduction (a : R) (m n : ℕ) : Quot a (m+n) →ₗ[R] Quot a n
theorem reduction_surjective (a : R) (m n : ℕ) :
    Function.Surjective (reduction a m n)
theorem exact (a : R) (m n : ℕ) :
    Function.Exact (inclusion a m n) (reduction a m n)
theorem inclusion_injective [IsDomain R] {a : R} (ha : a ≠ 0) (m n : ℕ) :
    Function.Injective (inclusion a m n)
```
Dependencies: Mathlib quotient linear maps and exactness only.
Anchors: `Submodule.mapQ`, `Submodule.mapQ_apply`, `Ideal.mem_span_singleton`,
`Submodule.Quotient.mk_eq_zero`, `Function.Exact`.
Apply later to a=p and the coordinates of a finite free coefficient module.
This does not construct compatible finite-flat models or a p-divisible group.

## W2 — IMPLEMENTED: self-twist trace support (cap 160 lines)

New `FLT/Deformations/RepresentationTheory/SelfTwistTrace.lean`.
The elementary character identity underlying the index-two case of [C].
For any representation over a field, conjugacy with its character twist
forces the trace to vanish where the character differs from one.
Namespace `Representation`; binders `k G V`, `[Field k] [Group G]`,
`[AddCommGroup V] [Module k V]`, `ρ : Representation k G V`:
```lean
theorem trace_eq_zero_of_selfTwist
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (hg : χ g ≠ 1) : LinearMap.trace k V (ρ g) = 0
```
Also expose the contrapositive at one element with nonzero trace. No
finite-dimensional hypothesis is necessary for this trace identity.
Dependencies: Mathlib `LinearAlgebra.Trace`, `RepresentationTheory.Basic`.
Anchors: `LinearMap.trace_conj'`, linearity of `LinearMap.trace`.
W4 must **construct** χ and e; W2 does not assume (A1) or prove it.

## W3 — IMPLEMENTED: tame spectrum excludes a nontrivial twist (cap 180 lines)

New `FLT/Deformations/RepresentationTheory/TameTraceObstruction.lean`.
Elementary final calculation needed after the finite-flat inertia-weight
classification [R]. Given eigenvalues a,b, an eigenvalue ratio of order
more than two prevents trace zero. In particular the ordinary ratio of
order p−1 and niveau-two ratio of order p+1 work for p≥17.
Namespace `Representation`, same binders as W2:
```lean
theorem add_ne_zero_of_orderOf_div_gt_two (a b : kˣ)
    (h : 2 < orderOf (a / b)) : (a : k) + (b : k) ≠ 0
theorem selfTwist_eq_one_of_tame_eigenvalues
    (χ : G →* kˣ) (e : V ≃ₗ[k] V)
    (he : ∀ g, e.conj (ρ g) = (χ g : k) • ρ g)
    (g : G) (a b : kˣ)
    (htrace : LinearMap.trace k V (ρ g) = (a : k) + (b : k))
    (horder : 2 < orderOf (a / b)) : χ g = 1
```
Add specializations with `17 ≤ p` and `orderOf (a/b) = p-1` or `p+1`.
Dependencies: W2, `orderOf_le_of_pow_eq_one`; the proof is that a+b=0
would force (a/b)^2=1. This is not the finite-flat inertia classification:
the eigenvalues, exact order, and trace formula must still be constructed.

## W4 — DONE: quadratic twist from cyclic restriction

Checked 2026-09-30 19:37 UTC: foreground builds, individual module lint,
and `#print axioms` passed for each new module; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Local commits:

| Leaf | Module | Lines / cap | Commit |
|---|---|---|---|
| W4a2 | `ThreeStableLines` | 83 / 150 | `03e0e1ce` |
| W4a3 | `CyclicScalarRestriction` | 85 / 180 | `c707386b` |
| W4a4 | `CyclicStableLinePair` | 57 / 100 | `f0ecade6` |
| Final | `CyclicRestrictionTwist` | 39 / 60 | `67ce77f8` |

All modules are under `FLT/Deformations/RepresentationTheory/`.
`Representation.exists_quadratic_selfTwist` takes `hV : finrank k V = 2`,
`hchar : (2 : k) ≠ 0`, irreducibility, and reducibility on the normal subgroup.
It constructs the nontrivial quadratic character, trivial on that subgroup,
and the conjugating linear equivalence. It needs an algebraically closed
field and cyclic quotient; finiteness of the quotient is unnecessary.
`exists_stableLines_pair_of_cyclic_quotient` proves the exact two-line orbit.
The existing `StableLinePair` and `PermutedSummandsTwist` supply the initial
complementary pair and the sign/intertwiner construction respectively.

## W5 — DONE: uniqueness of extension of a model morphism (cap 180 lines)

`FLT/GroupScheme/GenericFiberMapUnique.lean` (41 lines).
Checked 2026-09-30: foreground module build and per-module lint passed;
`#print axioms` for both declarations reports only standard axioms.
Mathlib `Algebra.TensorProduct.includeRight_injective` and
`IsFractionRing.injective` discharge injectivity; `Algebra.modelMap_unique`
needs flatness only for B and no Hopf structure.
A bounded first step toward model compatibility, not a claim of [R]'s
full existence/faithfulness theorem. For a domain O, its fraction field K,
and O-flat commutative Hopf algebras A,B, prove the following underlying
algebra-map statement (tensor inclusions are `TensorProduct.includeRight`):
```lean
theorem modelMap_unique (f g : A →ₐ[O] B)
    (h : (Algebra.TensorProduct.includeRight : B →ₐ[O] K ⊗[O] B).comp f =
         (Algebra.TensorProduct.includeRight : B →ₐ[O] K ⊗[O] B).comp g) : f = g
```
Dependencies discharged: the fraction-field tensor inclusion is injective
by the Mathlib localization/flatness API specialization above. W1 will feed
the compatible torsion-level maps.
Anchor: `FLT/GroupScheme/FiniteFlat.lean:Ideal.comapQuotientLinearMap_injective`
illustrates the existing torsion-free/injective-map conventions.

## Next arithmetic gate: tame detection of the cyclotomic quadratic character

Proposed leaves, in order; caps count whole new modules. D2–D3 require local
ramification proofs and remain source/API obligations. Split again if their
proofs exceed the caps; do not assume their conclusions in an input record.

1. D1 — DONE (cap 180): factor a character trivial on `ker ε` through `range ε`.
   For cyclic `range ε`, prove every generator detects a nontrivial factor;
   if its square is one and the coefficient characteristic is not two, its
   value on that generator is `-1`. This is a general group lemma.
   Implemented in `CharacterRange.lean` (92 lines): factorization, generator
   detection, and quadratic value `-1` (even without excluding characteristic
   two). Checked 2026-09-30: foreground build, module lint and all seven
   declarations’ axiom checks pass; standard axioms only.
2. D2 — DONE (cap 350): for an odd prime p, prove that the local extension
   `ℚ_p(μ_p)/ℚ_p` is totally ramified of degree p−1. Start from
   `cyclotomic_comp_X_add_one_isEisensteinAt` and the minimal polynomial of
   ζ_p−1; prove the ramification and residue-degree statements explicitly.
   Implemented in `LocalCyclotomicRamification.lean` (187 lines). Constructs
   an `IsCyclotomicExtension {p} ℚ_[p] E` with integral closure S, degree
   and ramification index p−1, and inertia degree 1; also proves irreducibility,
   degree and the shifted minimal polynomial in arbitrary field presentations.
   The result includes p=2. Checked 2026-09-30: foreground build, module lint,
   and all eleven theorem axiom checks pass (standard axioms only).
3. D3 — PARTIAL; local inertia/tame bridge remains (cap 350): use D2 to prove surjectivity of the mod-p cyclotomic
   character on local inertia at p. Identify this restriction with the
   level-one `tameCharacter` after identifying the residue field with `ZMod p`.
   Construct an inertia element whose tame value generates `(ZMod p)ˣ`.
   Reuse `FLT/AbsoluteGaloisGroup/TameCharacter.lean` and `InertiaComparison`.
   `LocalCyclotomicCharacter.lean` (124 lines) proves finite cyclotomic
   character surjectivity and constructs a finite Galois generator. It also
   constructs the local residue-field equivalence, proves its cardinality,
   cyclotomic naturality and the reduced geometric-sum ratio formula.
   Checked 2026-09-30: build, module lint and all ten declarations' axiom
   checks pass (standard axioms only). Absolute-inertia surjectivity and
   tame comparison are not proved. Remaining split: D3a presentation/action
   transport (220), D3b inertia lifting (200), D3c tame comparison (300),
   D3d generator transport (80). Exact targets are in the untracked handoff.
4. D4 — PARTIAL; inertia detector depends on D3b (cap 220): with ε the
   global mod-p cyclotomic character and H its
   kernel, use D1–D3 to produce an inertia element t with `χ t = -1` for
   every nontrivial quadratic χ trivial on H. Apply this to the χ constructed
   by W4. Prove the finite/cyclic quotient instances from `range ε`.

   `CyclotomicQuadraticDetection.lean` (101 lines) proves the actual global
   cyclotomic kernel quotient is finite and cyclic, constructs a simultaneous
   global detector, applies it to W4's self-twist, and proves compatibility
   of the global and local cyclotomic characters at the chosen local embedding.
   The detector is not yet proved to come from inertia. Remaining D4b (180)
   uses D3b and the proved `character_map_local` to choose it in inertia.
   Checked 2026-09-30: foreground build, module lint and all seven declarations’
   axiom checks pass (standard axioms only). The sibling GOAL-LIFTS-W7 lane in
   `wt-r1d` owns
   uniformizer-root inertia transitivity and tame surjectivity; reuse F4
   once validated, via D3c, as an alternative to D3a/D3b's direct route.

D4 supplies detection only. To contradict W3 at that same t, the finite-flat
inertia classification must still construct eigenvalues, their exact ratio
order p−1 or p+1, and the trace formula. `IsHardlyRamified.mem_isCompatible`
remains admitted; W4 alone does not discharge it.

## Gates still outside this wave

W1/W5 only address the algebra under the finite-flat → weight-two bridge.
One still needs existence of compatible model morphisms, exact integral
p-divisible levels, and the p-adic comparison theorem. [S, §1.2] defines
weight two using `(V ⊗ B_dR)^G` and graded ranks 1 in degrees 0 and −1.
No Galois de Rham/Hodge–Tate comparison API was found in FLT/Mathlib; do not
rename `IsFlatAt` to “weight two” or package that conclusion as input data.
These are future programs requiring further source splits, not ≤400-line leaves.
W2–W4 also need the finite-flat tame inertia spectrum and cyclotomic
quadratic-character detection before concluding (A1). This wave does not
replace `mem_isCompatible`, modify its statement, or discharge its admission.

## Recheck and acceptance

```sh
rg -n 'isAbsolutelyIrreducible|complexConjugation_fixed' FLT/GaloisRepresentation/HardlyRamified/AbsoluteIrreducibility.lean
rg -n 'class GaloisRep.IsFlatAt|HasFlatProlongationAt' FLT/Deformations/RepresentationTheory/GaloisRep.lean
rg -n 'isOpen.*|IsOpen' FLT/GaloisRepresentation/HardlyRamified/FlatCoefficientExtension.lean
rg -n 'trace_conj' .lake/packages/mathlib/Mathlib/LinearAlgebra/Trace.lean
rg -n 'mapQ_apply|def mapQ' .lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean
rg -n 'deRham|HodgeTate|BarsottiTate|quadratic_selfTwist' FLT .lake/packages/mathlib/Mathlib
```
The quadratic self-twist declaration is now present. W1–W3 declarations were
checked with `rg` in their named modules on 2026-09-30. Per leaf: foreground
`LEAN_NUM_THREADS=2 lake build MODULE`, `lake exe runLinter MODULE` alone,
`#print axioms` (standard axioms only), sorted `FLT.lean` import, local commit.
No push; no new axioms, admissions, arithmetic input records, or calls to
admitted arithmetic endpoints. Source caps count the entire new module.

Recheck W4 for each module in its table: `LEAN_NUM_THREADS=2 lake build MODULE`,
then `lake exe runLinter MODULE` separately. Import `CyclicRestrictionTwist`
and run `#print axioms Representation.exists_quadratic_selfTwist` for the
complete dependency audit. Check imports with
`grep '^public import' FLT.lean | LC_ALL=C sort -c`.
