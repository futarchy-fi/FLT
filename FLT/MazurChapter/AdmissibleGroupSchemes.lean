/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Admissible finite-flat group schemes over the integers

This file records the statement interfaces G1--G4 in the first Eisenstein-descent packet of
Mazur's torsion argument.  It deliberately stops before Néron models, Selmer groups and modular
curves.  The two representable elementary objects and their fppf realization are exposed as
temporary placeholder-backed interfaces so later packets can use the mathematically correct types
without pretending that the missing scheme-to-sheaf construction has already been formalized.

The statements follow Mazur, *Modular curves and the Eisenstein ideal* (1977), Chapter I, at the
lecture-level granularity of the Snowden Math 679 notes.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

namespace FLT.MazurChapter

/-- Finite-flat base object for audit nodes G1--G4 (Mazur 1977, I.1; Snowden Math 679):
a finite free commutative Hopf algebra over `ℤ` whose coproduct is cocommutative.  Finite freeness
is retained explicitly because it gives an unambiguous rank, hence the order of the represented
finite-flat commutative affine group scheme over `Spec ℤ`. -/
structure FiniteFlatCommGroupScheme where
  /-- The coordinate algebra of the affine group scheme. -/
  carrier : Type
  [commRing : CommRing carrier]
  [hopfAlgebra : HopfAlgebra ℤ carrier]
  [isFiniteFlat : HopfAlgebra.IsFiniteFlat ℤ carrier]
  [isFree : Module.Free ℤ carrier]
  /-- Cocommutativity of the coproduct, equivalently commutativity of the represented group. -/
  commutative :
    letI : HopfAlgebra ℤ carrier := hopfAlgebra
    letI : Bialgebra ℤ carrier := HopfAlgebraStruct.toBialgebra
    letI : Module ℤ carrier := Algebra.toModule
    letI : Coalgebra ℤ carrier := Bialgebra.toCoalgebra
    Nonempty (Coalgebra.IsCocomm ℤ carrier)

attribute [instance] FiniteFlatCommGroupScheme.commRing
  FiniteFlatCommGroupScheme.hopfAlgebra FiniteFlatCommGroupScheme.isFiniteFlat
  FiniteFlatCommGroupScheme.isFree

/-- Audit-node G1 base invariant (Mazur 1977, I.1; Snowden Math 679): the order of a finite-flat
group scheme over `Spec ℤ` is the `ℤ`-rank of its coordinate Hopf algebra. -/
noncomputable def FiniteFlatCommGroupScheme.order (G : FiniteFlatCommGroupScheme) : ℕ :=
  Module.finrank ℤ G.carrier

/-- Audit-node G1 coordinate object (Mazur 1977, I.1; Snowden Math 679), used to state
isomorphism without introducing a second, ad-hoc notion of affine group scheme. -/
abbrev FiniteFlatCommGroupScheme.coordinateAlgebra (G : FiniteFlatCommGroupScheme) :
    CommHopfAlgCat ℤ :=
  CommHopfAlgCat.of ℤ G.carrier

/-- Audit-node G1 isomorphism predicate (Mazur 1977, I.1; Snowden Math 679).  Hopf-algebra
isomorphism is contravariantly equivalent to isomorphism of the represented affine group schemes. -/
def FiniteFlatCommGroupScheme.Isomorphic
    (G H : FiniteFlatCommGroupScheme) : Prop :=
  Nonempty (G.coordinateAlgebra ≅ H.coordinateAlgebra)

/-- Audit node G1 elementary object (Mazur 1977, I.1; Snowden Math 679): the constant group
scheme `ℤ/pℤ` over `Spec ℤ`. -/
noncomputable def constantOrderPrime (p : ℕ) (_hp : p.Prime) :
    FiniteFlatCommGroupScheme := by
  sorry

/-- Audit node G1 elementary object (Mazur 1977, I.1; Snowden Math 679): the group scheme
`μ_p` over `Spec ℤ`. -/
noncomputable def multiplicativeOrderPrime (p : ℕ) (_hp : p.Prime) :
    FiniteFlatCommGroupScheme := by
  sorry

/-- Audit node G1 (Mazur 1977, I.1; Snowden Math 679): every finite-flat commutative group scheme
of prime order over `Spec ℤ` is isomorphic to the constant group `ℤ/pℤ` or to `μ_p`.  This is
only the order-`p` classification over `ℤ`, not a general Oort--Tate classification. -/
theorem order_prime_classification (p : ℕ) (hp : p.Prime)
    (G : FiniteFlatCommGroupScheme) (hG : G.order = p) :
    G.Isomorphic (constantOrderPrime p hp) ∨
      G.Isomorphic (multiplicativeOrderPrime p hp) := by
  sorry

/-- Audit-node G2 coefficient category (Mazur 1977, I.1; Snowden Math 679): abelian sheaves on
the fppf site of schemes. -/
abbrev FppfAbSheaf :=
  Sheaf (Scheme.fppfTopology : GrothendieckTopology Scheme.{0}) AddCommGrpCat.{0}

/-- Audit-node G2 representable-sheaf bridge (Mazur 1977, I.1; Snowden Math 679): the abelian
fppf sheaf of points represented by a finite-flat commutative affine group scheme. -/
noncomputable def fppfSheaf (_G : FiniteFlatCommGroupScheme) : FppfAbSheaf := by
  sorry

/-- Audit-node G2 exact-sequence relation (Mazur 1977, I.1; Snowden Math 679).  It says that the
represented fppf sheaves form a short exact sequence `0 → A → E → B → 0`. -/
def IsFppfShortExact
    (A E B : FiniteFlatCommGroupScheme) : Prop :=
  ∃ (f : fppfSheaf A ⟶ fppfSheaf E) (g : fppfSheaf E ⟶ fppfSheaf B)
      (h : f ≫ g = 0),
    (ShortComplex.mk f g h).ShortExact

/-- Audit-node G2 elementary-factor predicate (Mazur 1977, I.1; Snowden Math 679): a factor is
one of the two order-`p` group schemes classified by G1. -/
def IsElementary (p : ℕ) (hp : p.Prime) (G : FiniteFlatCommGroupScheme) : Prop :=
  G.Isomorphic (constantOrderPrime p hp) ∨
    G.Isomorphic (multiplicativeOrderPrime p hp)

/-- Audit node G2 (Mazur 1977, I.1; Snowden Math 679): an admissible group scheme has a finite
filtration whose nonzero factors are `ℤ/pℤ` or `μ_p`.  The index records the filtration length. -/
inductive IsAdmissible (p : ℕ) (hp : p.Prime) :
    ℕ → FiniteFlatCommGroupScheme → Prop
  | trivial {G} (hG : IsZero (fppfSheaf G)) : IsAdmissible p hp 0 G
  | elementary {G} (hG : IsElementary p hp G) : IsAdmissible p hp 1 G
  | extension {m n A E B}
      (hA : IsAdmissible p hp m A) (hB : IsAdmissible p hp n B)
      (hE : IsFppfShortExact A E B) : IsAdmissible p hp (m + n) E

/-- Audit node G2, extension closure (Mazur 1977, I.1; Snowden Math 679): an extension of two
admissible group schemes is admissible, with additive filtration length. -/
theorem admissible_extension (p : ℕ) (hp : p.Prime) {m n : ℕ}
    {A E B : FiniteFlatCommGroupScheme}
    (hA : IsAdmissible p hp m A) (hB : IsAdmissible p hp n B)
    (hE : IsFppfShortExact A E B) :
    IsAdmissible p hp (m + n) E :=
  .extension hA hB hE

/-- Audit node G2, subobject and quotient closure (Mazur 1977, I.1; Snowden Math 679): in a short
exact sequence with admissible middle term, both ends are admissible and their filtration lengths
add to that of the middle term. -/
theorem admissible_subobject_quotient (p : ℕ) (hp : p.Prime) {n : ℕ}
    {A E B : FiniteFlatCommGroupScheme} (hE : IsFppfShortExact A E B)
    (hAdmissible : IsAdmissible p hp n E) :
    ∃ a b : ℕ, a + b = n ∧ IsAdmissible p hp a A ∧ IsAdmissible p hp b B := by
  sorry

/-- Audit-node G3 cohomology bridge (Mazur 1977, I.2; Snowden Math 679): the additive group
`H^i_fppf(Spec ℤ, F)`.  Its eventual implementation is `Sheaf.H`; this declaration isolates the
currently missing small-universe Ext wiring without weakening any consumer statement. -/
noncomputable def fppfCohomology (_F : FppfAbSheaf) (_i : ℕ) : AddCommGrpCat := by
  sorry

/-- Audit node G3 (Mazur 1977, I.2; Snowden Math 679): the four elementary fppf-cohomology
computations over `Spec ℤ` for an odd prime `p`.  The additive equivalences are explicit finite
cardinality witnesses: the orders, in table order, are `p`, `1`, `1`, and `1`. -/
theorem elementary_fppf_cohomology (p : ℕ) (hp : p.Prime) (hpOdd : Odd p) :
    (Finite (fppfCohomology (fppfSheaf (constantOrderPrime p hp)) 0) ∧
        Nonempty
          ((fppfCohomology (fppfSheaf (constantOrderPrime p hp)) 0 : Type) ≃+
            ZMod p)) ∧
      (Finite (fppfCohomology (fppfSheaf (constantOrderPrime p hp)) 1) ∧
        Nonempty
          ((fppfCohomology (fppfSheaf (constantOrderPrime p hp)) 1 : Type) ≃+
            ZMod 1)) ∧
      (Finite (fppfCohomology (fppfSheaf (multiplicativeOrderPrime p hp)) 0) ∧
        Nonempty
          ((fppfCohomology (fppfSheaf (multiplicativeOrderPrime p hp)) 0 : Type) ≃+
            ZMod 1)) ∧
      (Finite (fppfCohomology (fppfSheaf (multiplicativeOrderPrime p hp)) 1) ∧
        Nonempty
          ((fppfCohomology (fppfSheaf (multiplicativeOrderPrime p hp)) 1 : Type) ≃+
            ZMod 1)) := by
  sorry

/-- Audit node G4 (Mazur 1977, I.2; Snowden Math 679): pure fppf dévissage bounds `H¹` of an
admissible group scheme of filtration length `n` by `p ^ n`.  The injection into the explicitly
finite function type states the bound without a cardinality operation with an infinite fallback. -/
theorem admissible_h_one_bound (p : ℕ) (hp : p.Prime) (hpOdd : Odd p) (n : ℕ)
    (G : FiniteFlatCommGroupScheme) (hG : IsAdmissible p hp n G) :
    Finite (fppfCohomology (fppfSheaf G) 1) ∧
      ∃ bound : fppfCohomology (fppfSheaf G) 1 → (Fin n → ZMod p),
        Function.Injective bound := by
  sorry

end FLT.MazurChapter
