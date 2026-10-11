/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Basic
public import FLT.Mazur.StandardSmoothFieldCotangentRank

/-!
# Field-valued cotangent rank through localization

The original affine differential module and its localization give the same
cotangent space at every field point of the localization. This preserves
ranks when passing between an affine chart and an actual local stalk.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedCotangentFieldRank

open TensorProduct

universe u

variable (R A L B : Type u) [CommRing R] [CommRing A] [CommRing L] [Field B]
  [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra A B] [Algebra L B] [IsScalarTower A L B]
  [Algebra.FormallyEtale A L]

/-- The actual field-valued cotangent spaces agree through a formally etale scalar step. -/
def fieldEquiv : (B ⊗[A] Ω[A⁄R]) ≃ₗ[B] (B ⊗[L] Ω[L⁄R]) :=
  (AlgebraTensorModule.cancelBaseChange A L B B Ω[A⁄R]).symm ≪≫ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L).baseChange L B _ _

/-- Passing to a local stalk preserves the rank of the original field cotangent space. -/
theorem finrank_eq :
    Module.finrank B (B ⊗[A] Ω[A⁄R]) = Module.finrank B (B ⊗[L] Ω[L⁄R]) :=
  (fieldEquiv R A L B).finrank_eq

/-- A cotangent rank computed on a stalk detects dimension on a standard-smooth chart. -/
theorem relativeDimension [Algebra.IsStandardSmooth R A] (d : ℕ)
    (hr : Module.finrank B (B ⊗[L] Ω[L⁄R]) = d) :
    Algebra.IsStandardSmoothOfRelativeDimension d R A :=
  (StandardSmoothFieldCotangentRank.relativeDimension_iff R A B d).mpr
    ((finrank_eq R A L B).trans hr)

end FLT.Mazur.LocalizedCotangentFieldRank
