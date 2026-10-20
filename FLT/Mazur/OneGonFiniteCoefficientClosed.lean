/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientPolynomial

/-!
# Descending the closed character embedding

Surjectivity descends by retaining polynomial preimages of every character
basis element. The result is the same character algebra over a finite-type
integer ring, not an unrelated finitely presented replacement.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A character-algebra map is surjective once its image contains the character basis. -/
theorem surjective_of_character_basis {A B G : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommMonoid G]
    (f : B →ₐ[A] AddMonoidAlgebra A G)
    (hf : ∀ g : G, AddMonoidAlgebra.single g (1 : A) ∈ Set.range f) :
    Function.Surjective f := by
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero f⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add f a b⟩
  | single g a =>
    obtain ⟨b, hb⟩ := hf g
    refine ⟨a • b, ?_⟩
    rw [map_smul, hb, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

variable {R G : Type*} [CommRing R] [AddCommMonoid G] [Finite G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)

/-- A finite enlargement of the coefficients makes the descended full map surjective. -/
theorem exists_surjective_model (hφ : Function.Surjective φ)
    (s : Set R) (hs : s.Finite) :
    ∃ s' : Set R, s'.Finite ∧ s ⊆ s' ∧
      Function.Surjective (modelCoordinates t j φ s') := by
  classical
  have hp (g : G) : ∃ p : MvPolynomial (Fin 3) R,
      φ (Ideal.Quotient.mk _ p) = AddMonoidAlgebra.single g 1 := by
    obtain ⟨b, hb⟩ := hφ (AddMonoidAlgebra.single g 1)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨p, hb⟩
  choose p hp using hp
  let s' : Set R := s ∪ ⋃ g, ((p g).coeffs : Set R)
  refine ⟨s', hs.union (Set.finite_iUnion fun g => (p g).coeffs.finite_toSet),
    Set.subset_union_left, surjective_of_character_basis _ ?_⟩
  intro g
  apply modelCoordinates_character_mem_range t j φ s' g (p g) _ (hp g)
  intro a ha
  exact Or.inr (Set.mem_iUnion.mpr ⟨g, ha⟩)

/-- The resulting closed coordinate model has finite-type integer coefficients. -/
theorem exists_finiteType_surjective_model (hφ : Function.Surjective φ)
    (s : Set R) (hs : s.Finite) :
    ∃ s' : Set R, s'.Finite ∧ s ⊆ s' ∧
      Algebra.FiniteType ℤ (modelRing t j φ s') ∧
      Function.Surjective (modelCoordinates t j φ s') := by
  obtain ⟨s', hs', hss', hsurj⟩ := exists_surjective_model t j φ hφ s hs
  exact ⟨s', hs', hss', modelRing_finiteType t j φ s' hs', hsurj⟩

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
