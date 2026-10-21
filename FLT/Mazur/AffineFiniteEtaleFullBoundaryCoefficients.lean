/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtaleBoundaryKernelTransition

/-!
# Literal full coefficients of simultaneous affine boundary lifts

Expose the underlying full-section equations before applying trace lifting to
large rank-stage expressions. All relation and boundary equations are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineFiniteEtaleFullBoundaryCoefficients
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)

include hf e in
/-- A full boundary coefficient has an invariant lift with literal section equality. -/
theorem exists_initial_lift
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ z : compatibleFunctions p q, J.subschemeι.appTop z.val = y.val := by
  obtain ⟨z, hz⟩ := AffineFiniteEtaleBoundarySurjectivity.ideal_invariant_surjective
    p q f hf e J hJ y
  exact ⟨z, congrArg Subtype.val hz⟩

variable {D' A' : Scheme.{0}} [IsAffine A'] (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  [IsClosedImmersion a] (I : A'.IdealSheafData) (hI : J.comap a = I)

include hf e H hq in
/-- Simultaneous lifting retains both literal full coefficient equations. -/
theorem exists_prescribed_lift
    (ρ : compatibleFunctions p q →+* compatibleFunctions p' q')
    (hρ : ∀ z, (ρ z).val = a.appTop z.val)
    (x : compatibleFunctions p' q')
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (hxy : I.subschemeι.appTop x.val =
      (IdealSheafClosedTransitions.map I J a hI).appTop y.val) :
    ∃ z : compatibleFunctions p q, ρ z = x ∧ J.subschemeι.appTop z.val = y.val := by
  obtain ⟨z, hz, hb⟩ := AffineFiniteEtaleBoundaryKernelTransition.exists_prescribed_lift
    p q f hf e p' q' a b H hq J hJ I hI x y hxy
  refine ⟨z, Subtype.ext ((hρ z).trans (congrArg Subtype.val hz)), congrArg Subtype.val hb⟩

end FLT.Mazur.AffineFiniteEtaleFullBoundaryCoefficients
