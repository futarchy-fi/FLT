# FAMILY-W3 — prerequisites for the two potential-modularity gates

Scope: the two gaps in `FAMILY_GOAL_LEDGER.md`, not GL* lifts or three-adic
sorting. Baseline `7a4bca25`; checked 2026-09-30 with the `rg` commands below.
F1–F3 are present. Snowden [S, §3 (A1), Thm. 5.1.2] requires **residual**
absolute irreducibility on the cyclotomic kernel, as well as weight two for
the characteristic-zero lift. Neither follows from the present global
absolute-irreducibility theorem by restriction alone.

This is a five-leaf **next wave**, not a claim that five small lemmas finish
both bridges. W1–W3 are ready and run in that order. W5 is now proved; W4
has checked partial results and is held for the remaining orbit-exhaustion
argument. Downstream work is named
explicitly; none is an assumed field in a new input record.

Sources: [S] Snowden, arXiv:0905.4266v1, §1.2, §3 and Thm. 5.1.2;
[R] Raynaud, *Schémas en groupes de type (p,...,p)*, BSMF 102 (1974),
Thm. 3.3.3 / Cor. 3.3.6 (the finite-flat model gate in the parent ledger);
[T] Tate, *p-divisible groups*, Proc. Conf. Local Fields (1967), §2
(the exact sequences required of torsion levels);
[C] Clifford, *Representations induced in an invariant subgroup*,
Ann. Math. 38 (1937), restriction to a normal subgroup.
Only [S]'s text is cached in `Scratch/snowden.txt`; [R]/[T]/[C] identify
source obligations, not a verified ready-to-import theorem in Lean.

## W1 — READY: coefficient torsion-level exactness (cap 220 lines)

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

## W2 — READY: self-twist trace support (cap 160 lines)

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

## W3 — READY: tame spectrum excludes a nontrivial twist (cap 180 lines)

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

## W4 — BLOCKED: quadratic twist from cyclotomic restriction (cap 400 lines)

W4a partial (2026-09-30): `StableLinePair.lean` (136 lines) proves
`exists_complementary_stableLines`, normal transport, and the preserve/swap
consequence conditional on exhaustion. Foreground build, per-module lint,
and standard-only axiom checks passed. The exact orbit-of-two result remains
open: three invariant lines force scalar H-action, and a cyclic quotient
then supplies a G-stable eigenline, contradicting irreducibility. These need
separate ≤150/180/100-line leaves (scalar lemma, cyclic eigenline, assembly);
no orbit-exhaustion conclusion is claimed.

W4b construction DONE conditional on W4a (2026-09-30):
`PermutedSummandsTwist.lean` (115 lines) constructs the sign character and
intertwiner. `exists_quadratic_selfTwist_of_stableLines_orbit` consumes exactly
the W4a target. Foreground build, per-module lint, and standard-only axiom
checks passed. The unconditional `exists_quadratic_selfTwist` still needs
W4a orbit exhaustion; no cyclic-restriction theorem is claimed.

Proposed `FLT/Deformations/RepresentationTheory/CyclicRestrictionTwist.lean`.
The rank-two, cyclic-quotient case of [C]. Exact target sketch, with
`[IsAlgClosed k] [FiniteDimensional k V]`, `hV : Module.finrank k V = 2`,
`H : Subgroup G`, `[H.Normal] [Finite (G ⧸ H)] [IsCyclic (G ⧸ H)]`:
```lean
theorem exists_quadratic_selfTwist
    (hirr : ρ.IsIrreducible) (hres : ¬ Representation.IsIrreducible (ρ.comp H.subtype)) :
    ∃ χ : G →* kˣ, χ ≠ 1 ∧ (∀ h : H, χ h = 1) ∧
      (∀ g, χ g ^ 2 = 1) ∧
      ∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g
```
Require characteristic ≠2 in the dispatch signature (e.g. `(2 : k) ≠ 0`).
Dependencies: a normal-subgroup stable-line orbit/decomposition lemma,
not yet found; W2 consumes the result. API anchors:
`Representation.IsIrreducible`, `Subrepresentation`, `MonoidHom.comp`
(with an explicit `Representation.IsIrreducible` application for restriction).
Do not dispatch the full Clifford theory in this cap. First build the
rank-two line-orbit lemma (≤200), then the sign character/intertwiner (≤200).
The arithmetic specialization additionally needs the mod-p cyclotomic
kernel, its quadratic quotient, and a tame inertia generator detecting it.
`AbsoluteIrreducibility.lean:isAbsolutelyIrreducible` supplies the **global**
input after scalar extension, not these missing restriction facts.

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
Last search found no such declaration. The existing prime-power openness
lemma is reused, not recreated as a new leaf. Per ready leaf: foreground
`LEAN_NUM_THREADS=2 lake build MODULE`, `lake exe runLinter MODULE` alone,
`#print axioms` (standard axioms only), sorted `FLT.lean` import, local commit.
No push; no new axioms, admissions, arithmetic input records, or calls to
admitted arithmetic endpoints. Source caps count the entire new module.

Held W4/W5 proposition sketches typechecked with explicit binders in
`Scratch/FamilyW3HeldSketches.lean` (no proof bodies); this validates types only.
