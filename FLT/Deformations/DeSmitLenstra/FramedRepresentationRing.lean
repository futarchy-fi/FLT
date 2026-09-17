/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The framed representation ring of a finite group

This file formalizes the generators-and-relations construction in de Smit--Lenstra,
*Explicit construction of universal deformation rings*, Section 3, equation (3.1).

For a group `G`, an index type `n`, and a commutative ring `O`, the commutative
`O`-algebra `FramedRepresentationRing O G n` has variables `X g i j` subject to
the relations saying that `X 1` is the identity matrix and `X (g * h) = X g * X h`.
Its universal representation induces the natural equivalence

`(FramedRepresentationRing O G n ->ₐ[O] A) ≃ (G ->* GL n A)`.

The construction is deliberately not called a completed group algebra. A group algebra is
generally noncommutative and nonlocal, whereas this coordinate algebra is commutative and is
the object actually used in the cited construction of the universal framed deformation ring.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace Deformation

variable (O : Type u) [CommRing O]
variable (G : Type v) [Group G]
variable (n : Type w) [Fintype n] [DecidableEq n]

/-- The polynomial algebra on the matrix entries of a `G`-indexed family of matrices. -/
abbrev FramedRepresentationPolynomial := MvPolynomial (G × (n × n)) O

/-- The identity and multiplication relations for the universal matrix-valued representation. -/
inductive FramedRepresentationRelation :
    FramedRepresentationPolynomial O G n → FramedRepresentationPolynomial O G n → Prop
  | one (i j : n) :
      FramedRepresentationRelation (MvPolynomial.X (1, (i, j))) (if i = j then 1 else 0)
  | mul (g h : G) (i j : n) :
      FramedRepresentationRelation (MvPolynomial.X (g * h, (i, j)))
        (∑ k, MvPolynomial.X (g, (i, k)) * MvPolynomial.X (h, (k, j)))

/-- The commutative coordinate algebra representing `n`-dimensional representations of `G`. -/
abbrev FramedRepresentationRing := RingQuot (FramedRepresentationRelation O G n)

/-- The quotient map from the polynomial algebra to the framed representation ring. -/
noncomputable def framedRepresentationQuotient :
    FramedRepresentationPolynomial O G n →ₐ[O] FramedRepresentationRing O G n :=
  RingQuot.mkAlgHom O (FramedRepresentationRelation O G n)

/-- The matrix of universal coordinate functions associated to `g : G`. -/
noncomputable def universalRepresentationMatrix (g : G) :
    Matrix n n (FramedRepresentationRing O G n) :=
  fun i j => framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j)))

@[simp]
lemma universalRepresentationMatrix_one : universalRepresentationMatrix O G n 1 = 1 := by
  apply Matrix.ext
  intro i j
  change framedRepresentationQuotient O G n (MvPolynomial.X (1, (i, j))) =
    if i = j then 1 else 0
  simpa [framedRepresentationQuotient] using
    (RingQuot.mkAlgHom_rel O
      (FramedRepresentationRelation.one (O := O) (G := G) i j))

@[simp]
lemma universalRepresentationMatrix_mul (g h : G) :
    universalRepresentationMatrix O G n (g * h) =
      universalRepresentationMatrix O G n g * universalRepresentationMatrix O G n h := by
  apply Matrix.ext
  intro i j
  change framedRepresentationQuotient O G n (MvPolynomial.X (g * h, (i, j))) =
    ∑ k, framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, k))) *
      framedRepresentationQuotient O G n (MvPolynomial.X (h, (k, j)))
  simpa [framedRepresentationQuotient] using
    (RingQuot.mkAlgHom_rel O (FramedRepresentationRelation.mul (O := O) g h i j))

/-- The universal representation of `G` over its framed representation ring. -/
noncomputable def universalRepresentation : G →* GL n (FramedRepresentationRing O G n) where
  toFun g :=
    { val := universalRepresentationMatrix O G n g
      inv := universalRepresentationMatrix O G n g⁻¹
      val_inv := by rw [← universalRepresentationMatrix_mul]; simp
      inv_val := by rw [← universalRepresentationMatrix_mul]; simp }
  map_one' := Units.ext (universalRepresentationMatrix_one O G n)
  map_mul' g h := Units.ext (universalRepresentationMatrix_mul O G n g h)

variable {O G n}

/-- Evaluate the coordinate algebra at a representation. -/
noncomputable def FramedRepresentationRing.ofRepresentation
    {A : Type*} [CommRing A] [Algebra O A] (ρ : G →* GL n A) :
    FramedRepresentationRing O G n →ₐ[O] A :=
  RingQuot.liftAlgHom O ⟨MvPolynomial.aeval fun x => ρ x.1 x.2.1 x.2.2, by
    intro x y h
    cases h with
    | one i j => simp [map_one, Matrix.one_apply]
    | mul g h i j => simp [map_mul, Matrix.mul_apply]⟩

@[simp]
lemma FramedRepresentationRing.ofRepresentation_generator
    {A : Type*} [CommRing A] [Algebra O A] (rho : G →* GL n A)
    (g : G) (i j : n) :
    FramedRepresentationRing.ofRepresentation rho
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j)))) =
      rho g i j := by
  simp [FramedRepresentationRing.ofRepresentation, framedRepresentationQuotient,
    RingQuot.liftAlgHom_mkAlgHom_apply]

/-- Apply an algebra homomorphism entrywise to the universal representation. -/
noncomputable def FramedRepresentationRing.toRepresentation
    {A : Type*} [CommRing A] [Algebra O A]
    (f : FramedRepresentationRing O G n →ₐ[O] A) : G →* GL n A :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp (universalRepresentation O G n)

@[simp]
lemma FramedRepresentationRing.toRepresentation_ofRepresentation
    {A : Type*} [CommRing A] [Algebra O A] (ρ : G →* GL n A) :
    FramedRepresentationRing.toRepresentation
      (FramedRepresentationRing.ofRepresentation (O := O) (G := G) (n := n) ρ) = ρ := by
  ext g i j
  simp [FramedRepresentationRing.toRepresentation,
    FramedRepresentationRing.ofRepresentation, universalRepresentation,
    universalRepresentationMatrix, framedRepresentationQuotient]

@[simp]
lemma FramedRepresentationRing.ofRepresentation_toRepresentation
    {A : Type*} [CommRing A] [Algebra O A]
    (f : FramedRepresentationRing O G n →ₐ[O] A) :
    FramedRepresentationRing.ofRepresentation
      (FramedRepresentationRing.toRepresentation (O := O) (G := G) (n := n) f) = f := by
  apply RingQuot.ringQuot_ext'
  apply MvPolynomial.algHom_ext
  rintro ⟨g, i, j⟩
  simp [FramedRepresentationRing.ofRepresentation,
    FramedRepresentationRing.toRepresentation, universalRepresentation,
    universalRepresentationMatrix, framedRepresentationQuotient]

/-- The universal property of the framed representation ring (de Smit--Lenstra (3.1)). -/
noncomputable def framedRepresentationEquiv
    {A : Type*} [CommRing A] [Algebra O A] :
    (FramedRepresentationRing O G n →ₐ[O] A) ≃ (G →* GL n A) where
  toFun := FramedRepresentationRing.toRepresentation (O := O) (G := G) (n := n)
  invFun := FramedRepresentationRing.ofRepresentation (O := O) (G := G) (n := n)
  left_inv := FramedRepresentationRing.ofRepresentation_toRepresentation
  right_inv := FramedRepresentationRing.toRepresentation_ofRepresentation

end Deformation
