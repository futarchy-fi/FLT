/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Full ideal equality from finite flat quotient degree

A surjective comparison of finite flat algebras of the same constant degree
is bijective. Consequently containment of two ideals with such quotients
is equality, including over nonreduced bases and at coincident orbit points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.FCurve

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Equal finite flat degree upgrades an onto algebra comparison to an isomorphism. -/
theorem bijective_of_surjective_of_finiteLocallyFreeDegree (d : ℕ)
    (hA : FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap R A))) d)
    (hB : FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap R B))) d)
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : Function.Bijective f := by
  let _ := finiteLocallyFreeDegree_moduleFinite R A d hA
  let _ := finiteLocallyFreeDegree_moduleFinite R B d hB
  let _ := finiteLocallyFreeDegree_moduleFlat R A d hA
  let _ := finiteLocallyFreeDegree_moduleFlat R B d hB
  apply Module.bijective_of_surjective_of_rankAtStalk_eq (φ := f.toLinearMap) hf
  intro m _
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq,
    finiteLocallyFreeDegree_residueFinrank R A d hA,
    finiteLocallyFreeDegree_residueFinrank R B d hB]

/-- The whole ideals agree when containment compares finite flat quotients of equal degree. -/
theorem ideal_eq_of_le_of_finiteLocallyFreeDegree (I J : Ideal A) (h : I ≤ J) (d : ℕ)
    (hI : FiniteLocallyFreeDegree
      (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) d)
    (hJ : FiniteLocallyFreeDegree
      (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J)))) d) : I = J := by
  have hi := (bijective_of_surjective_of_finiteLocallyFreeDegree d hI hJ
    (Ideal.Quotient.factorₐ R h) (Ideal.Quotient.factor_surjective h)).1
  apply le_antisymm h
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end FLT.Mazur.FCurve
