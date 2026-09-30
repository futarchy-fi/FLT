/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Functions on an affine node

Pairs of polynomial functions with the same value at the origin form a ring
pullback. Their inclusion is the kernel of the surjective difference of values.
This is local algebra, not a pushout assertion in the category of schemes.
-/

@[expose] public noncomputable section

open scoped Polynomial

namespace FLT.Mazur.PolygonNodeEqualizer

variable {R : Type*} [CommRing R]

/-- Polynomial pairs whose values agree at the node. -/
def A : Subalgebra R (R[X] × R[X]) :=
  AlgHom.equalizer ((Polynomial.aeval (0 : R)).comp (AlgHom.fst R _ _))
    ((Polynomial.aeval (0 : R)).comp (AlgHom.snd R _ _))

@[simp]
theorem mem_A (p : R[X] × R[X]) : p ∈ A (R := R) ↔ p.1.eval 0 = p.2.eval 0 := by
  simp [A, AlgHom.equalizer]

/-- Include node functions into functions on its two branches. -/
def inclusion : A (R := R) →ₐ[R] (R[X] × R[X]) := (A (R := R)).val

/-- Difference of the values on the branches at the origin. -/
def difference : (R[X] × R[X]) →ₗ[R] R :=
  ((Polynomial.aeval (0 : R)).comp (AlgHom.fst R _ _)).toLinearMap -
    ((Polynomial.aeval (0 : R)).comp (AlgHom.snd R _ _)).toLinearMap

@[simp]
theorem difference_apply (p : R[X] × R[X]) :
    difference p = p.1.eval 0 - p.2.eval 0 := by
  simp [difference]

theorem inclusion_injective : Function.Injective (inclusion (R := R)) :=
  Subtype.val_injective

/-- Exactness of the local normalization sequence at the branch functions. -/
theorem range_inclusion :
    LinearMap.range (inclusion (R := R)).toLinearMap = LinearMap.ker difference := by
  ext p
  simp only [LinearMap.mem_range, LinearMap.mem_ker, difference_apply, sub_eq_zero]
  constructor
  · rintro ⟨x, rfl⟩
    exact (mem_A _).mp x.property
  · intro h
    exact ⟨⟨p, (mem_A p).mpr h⟩, rfl⟩

theorem difference_surjective : Function.Surjective (difference (R := R)) := by
  intro r
  exact ⟨(Polynomial.C r, 0), by simp⟩

/-- Restriction to the first branch. -/
def first : A (R := R) →ₐ[R] R[X] := (AlgHom.fst R _ _).comp inclusion

/-- Restriction to the second branch. -/
def second : A (R := R) →ₐ[R] R[X] := (AlgHom.snd R _ _).comp inclusion

theorem first_second_agree :
    (Polynomial.aeval (0 : R)).comp (first (R := R)) =
      (Polynomial.aeval (0 : R)).comp second := by
  apply AlgHom.ext
  intro x
  exact x.property

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The ring pullback lift of two branch maps agreeing at the origin. -/
def lift (f g : B →ₐ[R] R[X])
    (h : (Polynomial.aeval (0 : R)).comp f = (Polynomial.aeval (0 : R)).comp g) :
    B →ₐ[R] A (R := R) :=
  (f.prod g).codRestrict A fun b ↦ AlgHom.congr_fun h b

@[simp]
theorem first_lift (f g : B →ₐ[R] R[X])
    (h : (Polynomial.aeval (0 : R)).comp f = (Polynomial.aeval (0 : R)).comp g) :
    first.comp (lift f g h) = f := rfl

@[simp]
theorem second_lift (f g : B →ₐ[R] R[X])
    (h : (Polynomial.aeval (0 : R)).comp f = (Polynomial.aeval (0 : R)).comp g) :
    second.comp (lift f g h) = g := rfl

/-- Maps into the node algebra are determined by both branch restrictions. -/
theorem hom_ext (f g : B →ₐ[R] A (R := R))
    (h₁ : first.comp f = first.comp g) (h₂ : second.comp f = second.comp g) : f = g := by
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  exact Prod.ext (AlgHom.congr_fun h₁ b) (AlgHom.congr_fun h₂ b)

theorem lift_unique (f g : B →ₐ[R] R[X])
    (h : (Polynomial.aeval (0 : R)).comp f = (Polynomial.aeval (0 : R)).comp g)
    (k : B →ₐ[R] A (R := R)) (h₁ : first.comp k = f) (h₂ : second.comp k = g) :
    k = lift f g h :=
  hom_ext k (lift f g h) h₁ h₂

end FLT.Mazur.PolygonNodeEqualizer
