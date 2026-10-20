/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtaleBoundaryKernelTransition

/-!
# Direct coefficient formulas for simultaneous boundary lifts

Seal the comparison with full invariant-ring restriction generically, so
named-domain specializations need only compare literal source coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineFiniteEtalePrescribedCoefficients
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {D' A' : Scheme.{0}} [IsAffine A'] (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  [IsClosedImmersion a] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : J.comap a = I)

include hf e hJ hI H hq in
/-- A simultaneous full invariant lift with both literal coefficient formulas. -/
theorem exists_lift (x : compatibleFunctions p' q')
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (hxy : I.subschemeι.appTop x.val =
      (IdealSheafClosedTransitions.map I J a hI).appTop y.val) :
    ∃ z : compatibleFunctions p q, a.appTop z.val = x.val ∧
      J.subschemeι.appTop z.val = y.val := by
  obtain ⟨z, hz, hb⟩ := AffineFiniteEtaleBoundaryKernelTransition.exists_prescribed_lift
    p q f hf e p' q' a b H hq J hJ I hI x y hxy
  exact ⟨z, congrArg Subtype.val hz, congrArg Subtype.val hb⟩

end FLT.Mazur.AffineFiniteEtalePrescribedCoefficients
