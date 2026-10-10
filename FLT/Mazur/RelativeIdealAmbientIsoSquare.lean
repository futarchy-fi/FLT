/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealAmbientHom

/-!
# Base change preserves commuting squares of ambient isomorphisms

A commuting square of original ambient morphisms gives a commuting square
of their actual base changes over every test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B A' B' S X : Scheme.{u}}
variable (a : A ⟶ S) (b : B ⟶ S) (a' : A' ⟶ S) (b' : B' ⟶ S)
variable (e : A ≅ B) (e' : A' ≅ B') (i : A ⟶ A') (j : B ⟶ B')
variable (he : e.hom ≫ b = a) (he' : e'.hom ≫ b' = a')
variable (hi : i ≫ a' = a) (hj : j ≫ b' = b)
variable (h : e.hom ≫ j = i ≫ e'.hom) (s : X ⟶ S)

include h in
/-- The commuting square of actual ambient comparisons survives arbitrary base change. -/
theorem relativeIdealAmbientIso_square :
    (relativeIdealAmbientIso e a b he s).hom ≫ relativeIdealAmbientHom b b' j hj s =
      relativeIdealAmbientHom a a' i hi s ≫ (relativeIdealAmbientIso e' a' b' he' s).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeIdealAmbientHom_fst, relativeIdealAmbientIso_hom_fst]
  · simp only [Category.assoc, relativeIdealAmbientHom_snd, relativeIdealAmbientIso_hom_snd,
      relativeIdealAmbientIso_hom_snd_assoc, relativeIdealAmbientHom_snd_assoc]
    rw [h]

end FLT.Mazur.ClosedIdealCover
