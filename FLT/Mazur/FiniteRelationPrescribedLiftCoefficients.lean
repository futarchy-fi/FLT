/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationPrescribedLifting

/-!
# Extracting simultaneous lifts through named coefficient maps

Compare coefficient maps generically before specializing their large geometric
arguments. The entire lower invariant and prescribed boundary value are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationPrescribedLifting
open SchemeEffectiveEpiSections
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : J.comap a = I)

/-- Extract simultaneous lifts using a named invariant map with its actual coefficient formula. -/
theorem exists_lift (H : HasLifts p q p' q' a J hJ I hI)
    (ρ : compatibleFunctions p q →+* compatibleFunctions p' q')
    (hρ : ∀ z, (ρ z).val = a.appTop z.val)
    (x : compatibleFunctions p' q')
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (hxy : I.subschemeι.appTop x.val =
      (IdealSheafClosedTransitions.map I J a hI).appTop y.val) :
    ∃ z : compatibleFunctions p q, ρ z = x ∧ J.subschemeι.appTop z.val = y.val := by
  rw [HasLifts] at H
  obtain ⟨z, hz, hb⟩ := H x y hxy
  exact ⟨z, Subtype.ext ((hρ z).trans hz), hb⟩

end FLT.Mazur.FiniteRelationPrescribedLifting
