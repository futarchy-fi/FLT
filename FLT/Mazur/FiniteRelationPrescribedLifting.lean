/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtalePrescribedCoefficients

/-!
# A sealed interface for simultaneous full boundary lifting

The interface keeps the geometric source and exact boundary fixed while
hiding coefficient elaboration from applications to large named schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationPrescribedLifting
open SchemeEffectiveEpiSections
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : J.comap a = I)

/-- Every compatible pair has a full invariant lift with both prescribed coefficients. -/
@[irreducible]
def HasLifts : Prop :=
  ∀ (x : compatibleFunctions p' q')
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)),
    I.subschemeι.appTop x.val = (IdealSheafClosedTransitions.map I J a hI).appTop y.val →
    ∃ z : compatibleFunctions p q, a.appTop z.val = x.val ∧
      J.subschemeι.appTop z.val = y.val

variable {S : Scheme.{0}} [IsAffine A] [IsAffine A'] [IsAffine S]
  (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  [IsClosedImmersion a]

include hf e H hq in
/-- Finite etale equivalence relations satisfy the simultaneous full boundary interface. -/
theorem hasLifts : HasLifts p q p' q' a J hJ I hI := by
  unfold HasLifts
  exact AffineFiniteEtalePrescribedCoefficients.exists_lift p q f hf e p' q' a b H hq J hJ I hI

end FLT.Mazur.FiniteRelationPrescribedLifting
