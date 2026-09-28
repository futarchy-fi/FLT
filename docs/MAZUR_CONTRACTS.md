# MZ1: contracts for the prime-level Mazur route

Source/code review: 2026-09-28; FLT `6b0261b42f006644b966243ac348d2e726ac020c`,
Mathlib `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
This refines G1/G2 of [MAZUR_PLAN.md](MAZUR_PLAN.md). It supplies contracts,
not constructions of modular curves or a proof of the torsion exclusion.

## Route decision and the exact FLT requirement

Retain Mazur's prime-level proof, Chapter III §5, pp. 156–160.
The bounded second review found no complete shorter proof from the existing
semistability, hardly-ramified, or category-D endpoints. This is a source
review result, not a claim that a shorter proof is impossible.

There are three different interfaces:

1. The **actual Frey caller** needs `FreyIrreducibility` below: irreducibility
   only for `P.freyCurve`, for a `FreyPackage P` with `17 ≤ P.p`.
   `FLT/Proof.lean` and `FLT/Assembly/Proof.lean` combine this with the
   opposite conclusion from the hardly-ramified machinery.
2. The **current conditional assembly** accepts
   `FLT.Assembly.MazurTorsionExclusion`: exclusion of `(Z/2)^2 × Z/p` on
   **every** elliptic curve over Q. This is a sufficient, stronger interface.
3. The **selected arithmetic route** proves `NoLargePrimeTorsion`, excluding
   a point of prime order at least 17 on every rational elliptic curve.
   The already-proved adapter gives interface 2 and then interface 1.

A clean proof of interface 1 would therefore suffice to replace the Mazur
input after a small assembly rewire. One need not prove a universal torsion
classification. No such proof is supplied by this review.

### The provenance that the current counterexample forgets

`FLT/FreyCurve/Mazur.lean`, `mazurW_counterexample_of_reducible`, has two
branches after the two filtration characters are shown to include a trivial
character:

- A trivial subcharacter gives rational p-torsion on the original Frey curve.
- A trivial quotient gives rational p-torsion on a **different** curve using
  `quotient_curve_of_trivial_quotient`. Full two-torsion survives its map.

The latter theorem exports an elliptic curve and an additive homomorphism
on rational points whose kernel is killed by p. Its signature does **not**
export an isogeny of schemes, its degree, semistability of the target, or a
Frey package for that target. Its construction uses Vélu, but those stronger
conclusions need separate theorems; an arbitrary additive homomorphism
with p-killed kernel cannot substitute for them.

Thus “only exclude p-torsion on the original Frey curve” does not cover both
branches. A useful restricted alternative must cover the original curve
**and its relevant degree-p quotient**, preserving actual geometric
provenance. The smaller direct input `FreyIrreducibility` avoids choosing
an incomplete notion of isogeny orbit.

The repo's mathematical exposition agrees with those two branches:
`blueprint/src/chapter/ch03freyold.tex`, lines 301–427, uses the universal
torsion theorem in both, and `ch02reductions.tex`, lines 188–203, cites
Serre (1987), §4.1, Proposition 6 for the reduction. This is a checked
secondary reference, not an independently reread proof of Serre's paper.
The newer Lean callers, rather than the old blueprint's implementation
status annotations, determine the interface audit above.

### Why the proposed shortcuts do not close it

- **Candidate** — Checked input and obstruction; Decision
- **Semistability plus full two-torsion implies hardly ramified** — `HardlyRamified/Defs.lean`
  additionally requires unramifiedness outside `{2,p}`, finite flatness at p, and a quotient at
  two. Semistability alone allows multiplicative inertia at other bad primes.; Insufficient
  hypotheses.
- **Apply the existing theorem to the original Frey representation** — `HardlyRamified/Frey.lean`
  proves it hardly ramified, then `torsion_not_isIrreducible` concludes **reducibility**. Rational
  p-torsion also gives reducibility.; No contradiction.
- **Apply category D to a reducible representation** — `CategoryDClassification.lean` allows
  constant-three and multiplicative-three constituents; these are not forbidden. Its objects are
  three-primary over `Z[1/2]`.; Wrong conclusion and different prime/base.
- **Use lifting/compatible families to obtain irreducibility** — `Assembly/Inputs.lean` starts
  lifting with irreducibility; `Assembly/PrimeField.lean` proves its negation.; Circular as a
  replacement for Mazur.
- **Bound torsion by reduction at 2 or 3** — `FreyCurve/Serre/AtTwo.lean` gives multiplicative
  reduction at 2. At split multiplicative reduction the component group can contain p-torsion.; No
  uniform local bound.
- **Use the special Frey discriminant at 2** — `two_pow_eight_mul_Δ_int` gives `v₂(Δ)=2p v₂(b)-8`,
  not divisible by p for p ≥17. This is promising for the original-curve branch, but degree-p Tate
  isogenies can multiply the valuation by p.; Does not exclude the quotient branch.
- **Composite level or a formal-immersion proof** — An injected group supplies a point of order
  2p, but not a ready classification of `X₁(2p)` or `X₀(2p)`. No such endpoint or formal-immersion
  package was found.; Adds missing global geometry.

The `HardlyRamified/...` paths in this table are under
`FLT/GaloisRepresentation/`. The discriminant observation is a proposed
local subargument, not a newly proved Lean result. The source itself warns
that the indispensable Step 3 is global: Mazur, III §5, p. 158.
The conclusion does not rely on treating existing declarations as trusted
proofs of their transitive dependencies.

## Source ledger and corrections to MZ0

[M] B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS
47 (1977), 33–186, [DOI](https://doi.org/10.1007/BF02684339),
[full PDF](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf).
Page numbers below are **printed page numbers**. The downloaded Numdam PDF
includes an initial cover, so PDF page 2 is printed page 33.

- **Contract / construction** — Exact source read; Scope
- **G1 coarse moduli and smooth integral curve away from p** — [M] II §1, pp. 62–64; `X₀(p)`
  agrees with the coarse model away from p; do not claim a universal elliptic curve over it.
- **G1 two disjoint rational cusp sections** — [M] II §1, p. 64; Remain disjoint under base change.
- **G1 integral section and cusp orientation** — [M] III §5, Step 3, p. 159; Base `Spec
  Z[1/(2p)]`; identity component corresponds to **zero**, outside it to **infinity**.
- **G2 Hecke correspondences and Eichler–Shimura** — [M] II §6, pp. 87–90; Actual algebraic
  correspondences, not only analytic modular-form operators.
- **G2 Eisenstein ideal** — [M] II §9, unnumbered definition, p. 95; Generated by `1+w` and
  `1+l-T_l` for primes l different from p.
- **G2 quotient construction** — [M] II §10, (10.3)–(10.4), pp. 97–98; Quotient by the subvariety
  generated by the completion-kernel ideal, **not** by `I·J`.
- **G2 good integral model** — [M] II §10, p. 98; Néron–Ogg–Shafarevich gives an abelian scheme
  over `Z[1/p]`, hence over our base.
- **G2 rational finiteness** — [M] III §3, Lemmas (3.2)–(3.4), Corollary (3.5), pp. 148–150; Uses
  Mordell–Weil, finite-flat cohomology and completion/support arguments.
- **G2 nonzero cusp image** — [M] introduction p. 35; III (3.1), p. 148; III §5, p. 160; Full
  (3.1) gives order `numerator((p-1)/12)`; client only needs distinct images.
- **G2 nonconstant projection and finite curve points** — [M] III (4.1), pp. 151–152; Nontrivial
  quotient, curve image generates it; finite fibers plus finite target points.
- **Integral specialization of torsion** — [M] III §5, pp. 159–160, footnote on p. 160; Includes
  residue-characteristic-primary torsion at odd primes; cites Oort–Tate.

Corrections: G1's modular-curve source is **II §1**, not I §1 (admissible
groups). The introduction's abbreviated G2 reading list refers to II §§6,
8, **10**, and Proposition 14.1; there is no proposed theorem “8.10”.
III §5 p. 159 prints a cross-reference “[7], VI, §5”; the relevant
moduli treatment is Deligne–Rapoport, listed as [9] in [M], and [M] II §1
identifies that source explicitly. Do not copy the inconsistent reference
as a checked independent citation.

[DR] P. Deligne and M. Rapoport, *Les schémas de modules de courbes
elliptiques*, LNM 349 (1973), 143–316. The construction dependencies are
II (generalized elliptic curves), IV (moduli and coarse spaces), VI §5
(cuspidal interpretation), VII §2 (cuspidal sections), as referenced in
[M]. Their precise independent page-level verification is a **construction
gate**, not something this bounded review claims to have completed; the
contracts above are directly supported by the checked pages of [M].

## Contract conventions and construction obligations

Fix a prime `p ≥ 17` for the final arithmetic. The geometric construction
should work for prime `p ≥ 5`; this also provides nonempty low-level test
cases instead of testing a functor only on an eventually empty set.
Use `T = Spec Z[1/(2p)]`. A rational point means an **over-category
morphism** from `Spec Q` with its specified map to T. It is not an arbitrary
underlying topological point of a scheme. Integral sections and reductions
are also morphisms, so their specialization equations include residue-field
information.

The code in the next section is one scratch compilation unit. It defines
propositions to prove about supplied data. In particular, a field of type
`G2Finite Q` in a record would be a hypothesis, not an implementation of
G2. No such record is installed in the proof spine.

The supplied data have these mandatory meanings:

- `M(U)` is the set of isomorphism classes of generalized elliptic curves
  with **ample cyclic finite locally free subgroup of rank p**, over U.
  Pullback defines its presheaf structure. Include degenerate polygons;
  using only smooth elliptic curves would describe the open modular curve.
  Over algebraically closed fields away from p, a smooth level structure
  is equivalently a cyclic subgroup of order p in geometric points.
  Over an arbitrary ring this equivalence is not a definition.
- `c : M ⟶ yoneda.obj X` is the coarse classifying transformation;
  `CoarseUniversal` and `CoarseGeometric` give its universal property and
  geometric-point bijection. They **do not** assert that `c.app U` is
  bijective for every U, or provide a universal family on X. In particular,
  isomorphism classes over Q do not parametrize coarse rational points
  bijectively: twists and descent matter.
- `m t` is the class of `(t.curve, <t.point>)`, using its finite étale
  subgroup scheme over Q. `G1Moduli` binds `primePoint` to this construction,
  so it cannot be an arbitrary assignment of points to X. Retain the
  generator separately for subsequent elliptic-curve arguments.
- `IntegralData.generic` and the residue maps `s` are the spectra of the
  canonical localization maps. `G1Extension` follows from properness over
  the Dedekind base; no universal elliptic family over the coarse space is
  being extended. It in fact holds for all rational points. The narrower
  signature is sufficient for this client.
- `ReductionData t q` must be constructed from the **Néron special fiber
  of t.curve at q**, with the identity section and reduction of rational
  points through `Q_q`. `residuePoint` is the unique point of `Spec F_q`.
  `InIdentity` uses its actual connected component. An arbitrary special
  cubic, or arbitrary supplied reduction map, is not an implementation.
  There is a different fiber for each t; no common fiber is assumed.
- `QuotientData.A` is the restriction to T of the Néron model of
  `J₀(p)/(γ_I J₀(p))`, where `γ_I = ⋂ₙ Iⁿ` and `γ_I J` is the abelian
  subvariety generated by the images of these endomorphisms. Its projection
  is `x ↦ [x-∞] ↦ A`. Prove it extends over T and is a morphism there.
  Do not confuse the kernel of completion with the Eisenstein ideal itself.

These are missing **data constructions**, not arbitrary predicate
parameters that can be assumed true. The scratch unit deliberately stops
short of defining generalized elliptic curves, Néron models or Jacobians:
they are not existing Mathlib types with the required universal properties.
The contracts are stable consumer interfaces; their producers must first
supply the semantic constructions above. A bare inhabitant of an
`IntegralData`/`QuotientData` record does not close any geometry leaf.

`MultiplicativeAt` quantifies over a change to a minimal local equation.
Mathlib's `HasMultiplicativeReduction R` is a property of a specified
minimal equation; applying it directly to an arbitrary rational
Weierstrass presentation would add an unintended minimality requirement.

`G1Specialization` excludes q=2 and q=p, and assumes multiplicative
reduction. The q=p argument remains a separate local leaf in A1/A3 of MZ0.
For the global Step 3, q=3 is available because p≥17. Odd-prime
specialization must include torsion whose order is divisible by q; only
prime-to-q injectivity is insufficient.

`G2Nonconstant` below records nonconstancy on rational points, already
implied by `G2Cusps`. To prove `G2Fibers`, use the stronger geometric fact:
the generic-fiber **scheme morphism** is nonconstant on a smooth proper
geometrically integral curve. The two rational cusp images establish that
fact; then every geometric fiber is zero-dimensional and finite. A
nonconstant function between sets alone does not imply finite fibers.

## Typechecked Lean contracts

All the following Lean blocks concatenate in order. No declaration is a
proof of a missing arithmetic theorem. The namespace keeps proposed API
names separate from existing FLT declarations.

```lean
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.ZMod.Basic
import FLT.FreyCurve.Basic
import FLT.EllipticCurve.Torsion
import FLT.FreyCurve.Serre.Semistable

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory AlgebraicGeometry Opposite
open scoped WeierstrassCurve.Affine

namespace MZ1

noncomputable section

abbrev SpecQ := Spec (CommRingCat.of ℚ)
abbrev BaseRing (p : ℕ) := Localization.Away (2 * (p : ℤ))
abbrev Base (p : ℕ) := Spec (CommRingCat.of (BaseRing p))
abbrev Sections {S : Scheme} (X : Over S) := Over.mk (𝟙 S) ⟶ X
abbrev Points {S : Scheme} (X : Over S) {K : Type} [CommRing K]
    (s : Spec (CommRingCat.of K) ⟶ S) := Over.mk s ⟶ X

structure PrimePoint (p : ℕ) where
  curve : WeierstrassCurve ℚ
  elliptic : curve.IsElliptic
  point : (curve⁄ℚ).Point
  order : addOrderOf point = p

-- This is the exact minimal input at the Frey caller, before choosing a torsion route.
def FreyIrreducibility : Prop :=
  ∀ P : FreyPackage, 17 ≤ P.p →
    letI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos)

-- A supplied moduli presheaf still has to be constructed from generalized elliptic curves.
def CoarseUniversal {S : Scheme} (X : Over S)
    (M : (Over S)ᵒᵖ ⥤ Type _) (c : M ⟶ yoneda.obj X) : Prop :=
  ∀ (Y : Over S) (t : M ⟶ yoneda.obj Y),
    ∃! f : X ⟶ Y, c ≫ yoneda.map f = t

def CoarseGeometric {S : Scheme} (X : Over S)
    (M : (Over S)ᵒᵖ ⥤ Type _) (c : M ⟶ yoneda.obj X) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S),
    Function.Bijective (c.app (op (Over.mk s)))

structure IntegralData (p : ℕ) where
  X : Over (Base p)
  generic : SpecQ ⟶ Base p
  cuspZero : Sections X
  cuspInfinity : Sections X
  primePoint : PrimePoint p → Points X generic

noncomputable def genericSection {p : ℕ} (D : IntegralData p)
    (x : Sections D.X) : Points D.X D.generic :=
  (Over.homMk D.generic (by simp) : Over.mk D.generic ⟶ Over.mk (𝟙 (Base p))) ≫ x

def G1Geometry {p : ℕ} (D : IntegralData p) : Prop :=
  IsProper D.X.hom ∧ SmoothOfRelativeDimension 1 D.X.hom ∧
  GeometricallyIntegral D.X.hom

def G1Cusps {p : ℕ} (D : IntegralData p) : Prop :=
  ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Base p),
    s ≫ D.cuspZero.left ≠ s ≫ D.cuspInfinity.left

def G1Noncuspidal {p : ℕ} (D : IntegralData p) : Prop :=
  ∀ t : PrimePoint p,
    D.primePoint t ≠ genericSection D D.cuspZero ∧
    D.primePoint t ≠ genericSection D D.cuspInfinity

def G1Extension {p : ℕ} (D : IntegralData p) : Prop :=
  ∀ t : PrimePoint p, ∃! x : Sections D.X, genericSection D x = D.primePoint t

-- The reduction morphisms are to the special fiber of the Neron model, not a cubic.
structure ReductionData {p : ℕ} (t : PrimePoint p) (q : ℕ) where
  fiber : Scheme
  residuePoint : Spec (CommRingCat.of (ZMod q))
  identity : Spec (CommRingCat.of (ZMod q)) ⟶ fiber
  reduce : (t.curve⁄ℚ).Point → (Spec (CommRingCat.of (ZMod q)) ⟶ fiber)

-- This uses the actual topological connected component in the special fiber.
def InIdentity {p q : ℕ} (t : PrimePoint p) (R : ReductionData t q) : Prop :=
  (R.reduce t.point) R.residuePoint ∈ connectedComponent (R.identity R.residuePoint)

def MultiplicativeAt (E : WeierstrassCurve ℚ) (q : ℕ) [Fact q.Prime] : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℚ_[q],
    (C • E.baseChange ℚ_[q]).HasMultiplicativeReduction ℤ_[q]

def G1Specialization {p : ℕ} (D : IntegralData p)
    (q : ℕ) (s : Spec (CommRingCat.of (ZMod q)) ⟶ Base p)
    (t : PrimePoint p) (R : ReductionData t q) : Prop :=
  (hq : q.Prime) → q ≠ 2 → q ≠ p →
  (letI : Fact q.Prime := ⟨hq⟩
   MultiplicativeAt t.curve q) →
  ∀ x : Sections D.X, genericSection D x = D.primePoint t →
    (s ≫ x.left = s ≫ D.cuspZero.left ↔ InIdentity t R) ∧
    (s ≫ x.left = s ≫ D.cuspInfinity.left ↔ ¬ InIdentity t R)

def G1Moduli {p : ℕ} (D : IntegralData p)
    (M : (Over (Base p))ᵒᵖ ⥤ Type _) (c : M ⟶ yoneda.obj D.X)
    (m : PrimePoint p → M.obj (op (Over.mk D.generic))) : Prop :=
  ∀ t, D.primePoint t = c.app _ (m t)

def EisensteinIdeal {T : Type} [CommRing T] (p : ℕ)
    (hecke : ℕ → T) (w : T) : Ideal T :=
  Ideal.span ({w + 1} ∪ {t | ∃ l : ℕ, l.Prime ∧ l ≠ p ∧ t = hecke l - 1 - l})

def EisensteinKernelIdeal {T : Type} [CommRing T] (I : Ideal T) : Ideal T :=
  ⨅ n : ℕ, I ^ n

structure QuotientData {p : ℕ} (D : IntegralData p) where
  A : Over (Base p)
  projection : D.X ⟶ A

noncomputable def onGeneric {p : ℕ} {D : IntegralData p}
    (Q : QuotientData D) : Points D.X D.generic → Points Q.A D.generic :=
  fun x => x ≫ Q.projection

def G2Abelian {p : ℕ} {D : IntegralData p} (Q : QuotientData D)
    [GrpObj Q.A] : Prop :=
  IsProper Q.A.hom ∧ Smooth Q.A.hom ∧ GeometricallyIntegral Q.A.hom ∧
  IsCommMonObj Q.A

def G2Finite {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  Finite (Points Q.A D.generic)

def G2Cusps {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  onGeneric Q (genericSection D D.cuspZero) ≠
    onGeneric Q (genericSection D D.cuspInfinity)

-- Finite fibers on rational points is the exact client consequence of nonconstancy.
def G2Fibers {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  ∀ a : Points Q.A D.generic, Finite {x : Points D.X D.generic // onGeneric Q x = a}

def G2Nonconstant {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  ¬ ∃ a : Points Q.A D.generic, ∀ x : Points D.X D.generic, onGeneric Q x = a

-- Whole-section injectivity is legitimate here only after all generic points are torsion.
def G2Specialization {p : ℕ} {D : IntegralData p} (Q : QuotientData D) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ p →
    ∀ s : Spec (CommRingCat.of (ZMod q)) ⟶ Base p,
      Function.Injective (fun a : Sections Q.A => s ≫ a.left)

def G2CurveFinite {p : ℕ} (D : IntegralData p) : Prop :=
  Finite (Points D.X D.generic)

end

end MZ1
```

For eventual theorem declarations, each `G1... D` or `G2... Q` is the
**result type**, after the canonical D/Q/R/M have been constructed. Pass
`hp : p.Prime` and `hp17 : 17 ≤ p` to their constructors/theorems. Geometry
can weaken `hp17` to `5 ≤ p`. `EisensteinIdeal` and its completion kernel
are definitions, not assertions of finiteness or nontriviality.

## Available API versus missing proofs

- **Contracts** — Existing, checked API; Still to construct/prove
- **`PrimePoint`, local reduction** — `WeierstrassCurve`, `Affine.Point`, `addOrderOf`,
  `VariableChange`, `HasMultiplicativeReduction`, padics; Finite étale subgroup scheme from the
  rational generator; relation to Néron component membership.
- **`CoarseUniversal`, `CoarseGeometric`, `G1Moduli`** — `CategoryTheory.Over`, `yoneda`,
  `NatTrans`, scheme pullbacks; Generalized elliptic moduli presheaf, coarse space, construction
  of the classifying transformation.
- **`G1Geometry`** — `IsProper`, `SmoothOfRelativeDimension`, `GeometricallyIntegral`; These
  instances for the constructed prime-level modular curve.
- **`G1Cusps`, `G1Noncuspidal`, `G1Extension`** — Scheme morphisms, `Spec.map`, localization,
  valuative criterion; Cusp charts and disjointness, smooth-pair noncuspidality, Dedekind-base
  section extension wrapper.
- **`G1Specialization`** — `connectedComponent`, morphism evaluation, local minimal equations;
  Néron special fibers, point reduction, polygon contraction and the oriented cusp comparison.
- **`EisensteinIdeal`, `EisensteinKernelIdeal`** — Ideals, powers, infima, completion algebra;
  Algebraic Hecke action on a modular Jacobian and the quotient by the specified subvariety.
- **`G2Abelian`** — `GrpObj` in `Over`, `IsCommMonObj`, proper/smooth/geometrically integral
  morphisms; Jacobian/Picard construction, abelian quotient, Néron extension, integral projection.
- **`G2Finite`** — Finite types and general module/sheaf-cohomology machinery; Mordell–Weil for
  this abelian variety, arithmetic fppf descent, support/completion argument.
- **`G2Cusps`** — Morphism inequality; finite cyclic group algebra; Nonzero cuspidal divisor image
  in this quotient, with auxiliary prime 2 included.
- **`G2Fibers`, `G2Nonconstant`, `G2CurveFinite`** — `LocallyQuasiFinite`,
  `Scheme.Hom.finite_preimage_singleton`, `Finite`; Curve-dimension argument and passage from
  scheme-theoretic finite fibers to finite rational fibers.
- **`G2Specialization`** — Composition of scheme morphisms; group-object points; Torsion
  specialization at odd primes, including q-primary torsion, and generic restriction injectivity.

Mathlib paths, relative to `.lake/packages/mathlib/Mathlib/`:
`AlgebraicGeometry/Over.lean`, `Group/Abelian.lean`, `Group/Affine.lean`,
`Morphisms/{Proper,Smooth,QuasiFinite}.lean`, `Geometrically/Integral.lean`,
`ValuativeCriterion.lean`, `EllipticCurve/{Reduction,VariableChange}.lean`,
`RingTheory/Localization/Away/Basic.lean`, and
`CategoryTheory/Sites/SheafCohomology/Basic.lean`.

`Group/Abelian.lean` is useful existing infrastructure: it proves a proper
geometrically integral group scheme over a field is commutative. It does
not construct Jacobians, quotients or prove Mordell–Weil. Mathlib's
`EllipticCurve/Jacobian/` files concern **coordinate formulas**, not the
Jacobian variety of a modular curve. The height file has ingredients for
Mordell–Weil, not the required general abelian-variety theorem.

The reusable FLT finite-flat realization starts at
`FLT/GroupScheme/FiniteFlat.lean`; inspect `Group/Affine.lean` before
building another Hopf-algebra/scheme bridge. The current
`FLT/MazurChapter/AdmissibleGroupSchemes.lean` has unfinished constant
objects, fppf realization, cohomology and classification declarations.
It does not discharge G2. Moreover, the G1/G2 numbering inside that file
is unrelated to G1/G2 in MZ0.

## The G2 arithmetic dependency gate

The elementary-looking assertion `Finite (A(Q))` hides the largest risk.
The actual qualitative proof read in [M] requires this chain:

1. Hecke algebra and integral Jacobian/Néron model. At the level prime p,
   its reduction and Tate modules supply the rank-one defect calculation
   of II §8, pp. 92–93. At an **auxiliary** Eisenstein prime l, the ordinary
   étale/multiplicative calculation supplies the other rank-one term.
2. II (14.1), pp. 113–114: the relevant finite-flat constituents are
   admissible. I §1, especially (1.7), bounds cohomology using the defect
   and multiplicative terms. The base is `Spec Z`, with finite flatness
   away from the **level p**. It is not the category-D base `Z[1/2]`.
3. III (3.2), pp. 148–149: these two rank estimates bound the orders of
   `H¹(S, J⁰[l^m]_P)` uniformly in m. A separate bound for each m is not
   enough. III (3.3) uses the Kummer sequence and its direct limit.
4. Mordell–Weil finite generation converts the bounded Kummer groups into
   vanishing of the corresponding rational rank. III (3.4)–(3.5),
   pp. 149–150, transfer this through the completion-support quotient.
5. Nonzero cusp image is a separate obligation. Full III (3.1) would
   supply it but proves more than needed; isolate only injectivity on a
   nonzero cuspidal element when porting the proof.

Do not drop auxiliary l=2: for level p=17 the cuspidal order is 4,
so an odd-auxiliary-prime-only argument misses a case in the FLT range.
MZ0's three-primary Fontaine/Ext leaves cannot be renamed to arbitrary l.
Mordell–Weil, Néron representability and this fppf arithmetic must have
explicit owners before dispatching the descent package.

## Bounded leaves and dispatch order

All line counts below are **new Lean lines per leaf**, including local
support lemmas, estimated after the listed prerequisites exist. No leaf
may hide a new general foundation inside a proof or close by assuming its
own result. Stop and split if a proof grows past about 500 lines. Hours
are rough worker-hours for implementation and local checking, not elapsed
fleet time or a delivery promise. Only the first three are dispatchable
immediately. Later estimates are contingent on their construction gates.

### First three dispatchable leaves

**L01 — over-category point and section operations.** 120–220 lines,
4–8 hours; dependencies: current Mathlib. Implement a reusable file with
`Sections`, `Points`, restriction along a map to the base, and
postcomposition. Prove restriction/postcomposition commute, including
equality as over-morphisms rather than only underlying point functions.
This is the composition algebra used by G1Extension/G2Specialization;
source: the section diagram in [M] III §5, pp. 159–160.
Acceptance: both composite morphisms reduce to the same scheme morphism,
with the over-base equation checked by Lean. No arithmetic assumptions.

**L02 — canonical maps for the integral base.** 160–300 lines, 5–10 hours;
depends on L01. Construct `Z[1/(2p)] →+* Q` and, for prime q different
from 2 and p, `Z[1/(2p)] →+* ZMod q`, using
`IsLocalization.Away.lift`. Prove uniqueness and their agreement on Z;
use `Spec.map` and L01 to expose the generic/residue restriction maps.
Acceptance: q=3 is constructible under `p.Prime` and `17 ≤ p`; q=2 or p
is rejected by the required unit hypothesis, not given an arbitrary map.
Source: [M] III §5, p. 159.

**L03 — the two-cusp collision consumer.** 100–200 lines, 3–7 hours;
depends on L01–L02. Given `IntegralData`, `QuotientData`, `G2Cusps` and
`G2Specialization`, show that a section cannot specialize to infinity at
3 and zero at another allowed prime. Postcompose the two equalities;
specialization injectivity identifies the projection of the section with
both cusp sections; generic restriction contradicts `G2Cusps`.
Acceptance: build a conditional theorem using only those inputs. This
closes the diagram chase, **not** G1, G2, or Mazur. Source: [M] III §5,
pp. 159–160. It tests that the contracts contain the data the client uses.

### G1 construction leaves

The following grouped lists name **separate** leaves, with stable suffixes.
Every item has the per-leaf size/time allowance stated for its group.
Dependencies refer to previously defined groups; they are not permission
to treat an unbuilt foundational theorem as available.

**G1-A, generalized-curve data** — each 200–450 lines, 10–30 hours;
after L01–L02. Source: [M] II §1, p. 62, and its [DR] II dependency.

- A1: define a proper flat genus-one family, smooth-locus group and action
  data, using scheme morphisms and actual relative curves.
- A2: define morphisms/isomorphisms of that data and their composition.
- A3: implement pullback of the data and the identity/composition isomorphisms.
- A4: define a finite locally free subgroup of specified rank in the smooth locus.
- A5: define cyclic level via its effective Cartier divisor, and its pullback.
- A6: express ampleness of the subgroup divisor; separate smooth fibers
  from polygon fibers. Verify this on the split p-gon once G1-B is available.
- A7: form isomorphism classes and the pullback presheaf M from A1–A6.
- A8: embed a rational exact-order point as the finite étale subgroup
  generated by it and construct `m`; prove change-of-generator invariance.

A1 depends on the curve/cohomology foundation gate below; A5 depends on
the divisor gate. Definitions alone do not prove the geometric fibers
are elliptic curves or Néron polygons. A6's polygon verification follows B;
A7 can use its definition before that verification, so there is no cycle.

**G1-B, cuspidal charts** — each 200–500 lines, 15–40 hours;
after A1–A5 and the gluing/divisor foundation gate.
Source: [M] II §1, p. 64; III §5, p. 159; [DR] II, VI §5, VII §2.

- B1: construct the split n-gon by the indexed projective-line gluing maps.
- B2: identify its smooth locus with `G_m × Z/n` and construct its group action.
- B3: construct the transverse cyclic subgroup and check rank and ampleness.
- B4: construct the identity-component cyclic subgroup and its contracted
  generalized curve. Do not call a nonample pair on a p-gon a moduli object.
- B5: construct the two resulting cusp sections of the coarse model after C.
- B6: prove their disjointness, including over residue characteristic three.

B5–B6 await G1-C's coarse model; B1–B4 provide its boundary input.
The picture on [M] p. 159 describes the component membership; the
contraction in B4 is needed when translating that picture into the ample
level convention used for M.

**G1-C, coarse curve** — each 200–500 lines, 15–50 hours;
after A7 and B1–B4, and the coarse-moduli foundation gate.
Source: [M] II §1, pp. 62–64.

- C1: construct the auxiliary rigidified level atlas and its relation.
- C2: form its coarse quotient and descend the transformation c.
- C3: prove `CoarseUniversal` for c from the quotient's universal property.
- C4: prove `CoarseGeometric` for c, including boundary points.
- C5: descend properness away from p.
- C6: prove smooth relative dimension one away from p, including characteristic 3.
- C7: prove geometric integrality of the fibers on that base.
- C8: construct `primePoint` through c and prove `G1Moduli`/`G1Noncuspidal`.

C1/C2 are atlas/quotient **applications** after the foundation theorem;
construction of general quotients is not hidden in their 500-line budget.

**G1-D, extension and local interpretation** — each 150–450 lines,
10–35 hours; after C and the Néron/Tate-model foundation gate.
Source: [M] III §5, p. 159.

- D1: prove extension of a rational point on a proper T-scheme across each DVR.
- D2: glue the local extensions and prove uniqueness; specialize to `G1Extension`.
- D3: construct `ReductionData` from the Néron model and its extension of points.
- D4: compare the smooth minimal equation's identity subgroup with `InIdentity`.
- D5: compare the multiplicative local level pair with B3/B4 after splitting.
- D6: descend that comparison in the nonsplit case and prove `G1Specialization`.

D1–D2 can start before D3–D6; D5–D6 are local statements at allowed q,
not the global assertion that the torsion point is outside every identity component.

### G2 construction leaves

**G2-A, Jacobian and Hecke applications** — each 200–500 lines,
15–50 hours; after G1-C and the Picard/Jacobian foundation gate.
Source: [M] II §§6, 8, 10, pp. 87–93, 97–98.

- A1: construct `J₀(p)` from the Picard functor and the Abel–Jacobi map based at infinity.
- A2: construct the Fricke involution and prove that it exchanges the cusps.
- A3: construct the two degeneracy maps for an auxiliary prime and their finite fibers.
- A4: induce `T_l` by pullback/pushforward on the Jacobian.
- A5: prove the required Hecke commutation relations and define their commutative algebra T.
- A6: prove T is finite over Z and identify the rational factor decomposition needed by §10.
- A7: construct the bad-level toric part and identify its rank after Eisenstein completion.
- A8: identify the ordinary étale/multiplicative ranks at auxiliary Eisenstein primes.

A3 needs auxiliary-level moduli, a real additional dependency even though
the final target uses prime level. A6–A8 are applications of the relevant
comparison/duality foundation theorems, not substitutes for those proofs.

**G2-B, quotient and cuspidal image** — each 150–450 lines,
10–35 hours; after G2-A and the abelian-quotient/Néron foundation gate.
Source: [M] II §9, p. 95; II §10, pp. 97–98; III §3, pp. 148–150.

- B1: identify the explicit `EisensteinIdeal` with the Hecke-eigenvalue kernel.
- B2: identify `EisensteinKernelIdeal` with the kernel of I-adic completion.
- B3: construct the subvariety generated by its endomorphism images and form the quotient.
- B4: prove good reduction of that quotient away from p and restrict its Néron model to T.
- B5: extend Abel–Jacobi followed by the quotient to T, obtaining `QuotientData`/`G2Abelian`.
- B6: compute the cuspidal divisor's order `numerator((p-1)/12)` in J.
- B7: prove its nonzero image in A; include the 2-primary case.
- B8: deduce `G2Cusps`, checking the p≥17 numerical inequality separately.

B6 requires the modular-unit/divisor computation and B7 the relevant
cuspidal subgroup argument; neither follows from the definition of I.
If porting full III (3.1) to obtain B7, wait for G2-C; there is no use of
B7 in the rank/finiteness part of C, so this alternative is acyclic.

**G2-C, qualitative descent applications** — each 200–500 lines,
20–60 hours; after G2-A/B and the arithmetic cohomology/Mordell–Weil gates.
Source: [M] I §1, pp. 43–49; II (14.1), pp. 113–114;
III (3.2)–(3.5), pp. 148–150.

- C1: identify the finite group schemes `J⁰[l^m]_P` and their admissible filtration.
- C2: prove the defect term is `m g_P + O(1)` with a bound independent of m.
- C3: prove the multiplicative term has the same leading term and a uniform error.
- C4: apply the cohomology inequality to obtain a uniform cardinal bound on H¹.
- C5: construct the Kummer maps and prove their compatibility as m increases.
- C6: pass to the direct limit and eliminate the completed Mordell–Weil free rank.
- C7: prove the rational-point functor is exact after tensoring with Q for the quotients used.
- C8: transfer the rank vanishing across the completion/support quotient, then prove `G2Finite`.

C1 requires II (14.1), including its arithmetic proof, not a field named
“admissible”. C6 uses the independently proved Mordell–Weil finite-generation
theorem. C7 is not integral surjectivity on rational points.

**G2-D, downstream consumers** — each 100–400 lines, 5–20 hours;
after the specified contracts. Source: [M] III (4.1), pp. 151–152;
III §5, pp. 159–160.

- D1: from `G2Cusps`, prove nonconstancy of the generic scheme morphism and `G2Nonconstant`.
- D2: show a nonconstant map from the smooth proper integral curve has zero-dimensional fibers.
- D3: convert those fibers to finite rational-point fibers, proving `G2Fibers`.
- D4: combine `G2Fibers` and `G2Finite` to prove `G2CurveFinite`.
- D5: prove torsion specialization injectivity at odd good primes using the finite-flat local gate.
- D6: use finite rational points and separatedness to prove `G2Specialization` for all sections.
- D7: combine L03 with G1Specialization and the small-prime local facts to finish MZ0's Step 3.

D2–D3 need the curve-dimension foundation gate. D5 must handle q-primary
torsion; it cannot be replaced by the existing elliptic prime-to-q argument.

### Foundation gates and realistic totals

The application leaves above are a decomposition, **not** evidence that
their prerequisites fit into one more 500-line task. Each foundation is
itself a port, with the following bounded leaf families. A family is not a
single dispatchable leaf: instantiate one leaf per named construction,
base-change lemma or cited proof lemma, each 200–500 lines / 15–60 hours.
Before opening its implementation queue, pin the exact source lemma list
and its statements. If that cannot be done, keep the family gated; do not
send an agent a task called “construct the Jacobian, ≤500 lines”.

- **F-Curve (8–16 leaves):** relative genus/cohomology definition;
  base-change invariance; effective Cartier divisors; divisor pullback;
  finite-flat degree; ampleness criterion; proper relative curves;
  dimension-one image/fiber lemmas. Unblocks G1-A and G2-D.
  Source entry: [M] II §1, pp. 62–64; III (4.1), pp. 151–152, and [DR] II.
- **F-Moduli (12–30 leaves):** rigidified level atlas; atlas isomorphisms;
  relation/groupoid; finite group quotient charts; invariant coordinate
  rings; quotient-chart gluing; proper descent; geometric orbits;
  exceptional-automorphism local charts at j=0 and 1728; boundary charts;
  contraction and base change; coarse universal property. Reuse generic
  descent theorems only after their hypotheses are checked. Unblocks G1-C.
  Source entry: [M] II §1, pp. 62–64 and its [DR] IV references.
- **F-Picard (12–30 leaves):** divisor classes; line-bundle functor;
  rigidification; relative Picard representability; identity component;
  Jacobian smoothness/properness; group structure; Abel–Jacobi;
  pullback/norm; duality; abelian subvariety image and quotient;
  extension of maps. Unblocks G2-A/B. Source entry: [M] II §6,
  pp. 88–89; II §10, pp. 97–98. Representability requires its own
  source-lemma subdivision, not merely a definition of a desired property.
- **F-Neron (8–20 leaves):** local smooth model; mapping property;
  uniqueness and gluing; special fiber; component subgroup;
  good-reduction abelian model; quotient good reduction;
  extension of group maps. Unblocks G1-D/G2-B. Source entry:
  [M] II §10, p. 98; III §5, pp. 157–160, and the appendix, pp. 173–183.
- **F-Arithmetic (15–40 leaves):** finite-flat to sheaf realization;
  connected/étale parts; elementary constant/multiplicative cohomology;
  quasi-finite extensions at the level prime; exact-sequence cardinal
  inequalities; admissible filtration; defect formulas; Galois
  constituent comparison; auxiliary characteristic-two cases;
  local torsion-specialization rigidity. Unblocks G2-A/C/D. Source entry:
  [M] I §1, pp. 43–49; II §8, pp. 92–93; II (14.1), pp. 113–114;
  III (3.2), p. 148; III §5, p. 160. The auxiliary two case is a distinct
  branch of this queue, not an invocation of an odd-prime lemma.
- **F-MW (10–25 leaves):** abelian-variety heights; local/global height
  comparison; weak Mordell–Weil for the needed isogenies; finite Selmer
  inputs; height descent; finite generation; rational exactness up to
  torsion; completion/support commutative algebra. Unblocks G2-C.
  Source entry: the explicit Mordell–Weil use in [M] III (3.3)–(3.5),
  pp. 149–150. General abelian-variety finite generation is currently a
  source-design gate; the elliptic height file alone is insufficient.

The family counts are planning allowances, not a claim that all those
proofs have already been reduced to independent 500-line lemmas. **Do not
release these families en masse from this document.** Release L01–L03,
then the concrete data definitions, and require the next source-lemma
contracts before each foundational port. This records the real uncertainty
instead of assigning fictitious small sizes to deep existence theorems.

There are 28 G1 application leaves, 31 G2 application leaves, and L01–L03;
the family budgets add roughly 65–161 foundational leaves. The counts
illustrate the scale and should not be treated as a fixed task graph.
MZ0's G1/G2 allowances of 8,000–20,000 and 12,000–35,000 lines remain
plausible only with extensive foundations shared or available. Reserve a
further **20,000–50,000 lines / 2,000–5,000 worker-hours** for the missing
generic foundations, deduplicating overlap with G1/G2 during source design.
A conservative G1+G2 planning envelope is therefore **40,000–105,000 lines /
4,000–10,500 worker-hours**. These are uncertain engineering estimates;
A1–A4 of MZ0 are additional work. This review does not justify a shorter
calendar estimate or immediate parallel dispatch of all packages.

The dependency order is:

```text
L01 -> L02 -> L03 (conditional diagram chase)
F-Curve -> G1-A -> G1-B1..B4 -> F-Moduli -> G1-C -> G1-B5..B6
G1-C + F-Neron -> G1-D -> integral modular interpretation
G1-C + F-Picard + F-Arithmetic -> G2-A
G2-A + F-Neron + abelian quotient foundation -> G2-B1..B5
G2-A/B1..B5 + F-Arithmetic + F-MW -> G2-C -> G2Finite
cuspidal calculation (+ G2-C if using full III (3.1)) -> G2-B6..B8
G1Geometry + G2Cusps -> G2-D1..D3 -> G2Fibers
G2Finite + G2Fibers -> G2CurveFinite
G2Abelian + G2Finite + F-Arithmetic -> G2-D5..D6 -> G2Specialization
L03 + G1Specialization + small-prime local facts -> G2-D7
```

No path uses `FreyPackage.mazur`, `mazur_W`, `Mazur_statement`, or the
finished FLT theorem to prove any of these inputs. Subsequent proof leaves
must inspect transitive dependencies, not just scan their own source.

## Reproducing the contract and repository checks

This delivery adds documentation only. The complete Lean unit is embedded
above so the check does not depend on an untracked scratch file surviving.
Extract and check it from this worktree:

```sh
python3 - <<'PY'
from pathlib import Path
import re
text = Path('docs/MAZUR_CONTRACTS.md').read_text()
blocks = re.findall(r'^```lean\n(.*?)^```', text, re.M | re.S)
Path('/tmp/MazurContracts.lean').write_text('\n'.join(blocks))
PY
lake env lean /tmp/MazurContracts.lean
```

`autoImplicit` and `relaxedAutoImplicit` are explicitly false in the unit.
The build checks types of contracts, **not** proofs of the propositions.
Existing imported FLT modules are not certified free of assumptions by
this typecheck. No Lean module or import list is changed, so no new module
build, FLTTest regeneration, or changed-module linter is required.

Repository checks: compare the `import FLT.*` list in `FLT.lean` with all
`.lean` paths under `FLT/`, sorted bytewise (`LC_ALL=C`); check both equality
and count, run `git diff --check`, and check this document's line lengths.
Checked 2026-09-28 at 10:57 UTC: the extracted unit exited 0 with no
warnings; all 987 FLT imports match the 987 source modules in byte order;
document/Lean lines are at most 100 characters; the embedded Lean contains
none of the prohibited proof shortcuts; `git diff --check` passed.
The final local commit IDs are recorded in `LAST.txt`.
