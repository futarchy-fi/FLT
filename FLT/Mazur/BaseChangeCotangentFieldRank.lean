/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StandardSmoothFieldCotangentRank
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Actual cotangent fibers under cartesian change of coefficients

The differential module of a pushout is the base change of the original
algebraic differentials. Evaluating at any field point preserves the actual
cotangent fiber, including at points of a closed fiber.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BaseChangeCotangentFieldRank

open TensorProduct

universe u

variable (R S A C B : Type u) [CommRing R] [CommRing S] [CommRing A]
  [CommRing C] [Field B] [Algebra R S] [Algebra R A] [Algebra R C]
  [Algebra S C] [Algebra A C] [IsScalarTower R S C] [IsScalarTower R A C]
  [Algebra.IsPushout R S A C]
  [Algebra A B] [Algebra C B] [IsScalarTower A C B]

/-- A cartesian change of coefficients preserves the cotangent fiber at a field point. -/
def fieldEquiv : (B ⊗[A] Ω[A⁄R]) ≃ₗ[B] (B ⊗[C] Ω[C⁄S]) :=
  (AlgebraTensorModule.cancelBaseChange A C B B Ω[A⁄R]).symm ≪≫ₗ
    (KaehlerDifferential.tensorKaehlerEquiv R S A C).baseChange C B _ _

/-- The original and changed-coefficient differential fibers have equal ranks. -/
theorem finrank_eq :
    Module.finrank B (B ⊗[A] Ω[A⁄R]) = Module.finrank B (B ⊗[C] Ω[C⁄S]) :=
  (fieldEquiv R S A C B).finrank_eq

/-- A fiber rank computes the relative dimension of an original standard-smooth chart. -/
theorem relativeDimension [Algebra.IsStandardSmooth R A] (d : ℕ)
    (hr : Module.finrank B (B ⊗[C] Ω[C⁄S]) = d) :
    Algebra.IsStandardSmoothOfRelativeDimension d R A :=
  (StandardSmoothFieldCotangentRank.relativeDimension_iff R A B d).mpr
    ((finrank_eq R S A C B).trans hr)

end FLT.Mazur.BaseChangeCotangentFieldRank
