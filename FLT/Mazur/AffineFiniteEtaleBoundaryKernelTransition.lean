/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteEtaleSimultaneousLifting
public import FLT.Mazur.IdealSheafClosedTransitions

/-!
# Surjectivity on full boundary kernels of closed relation transitions

A lower invariant and a prescribed higher boundary invariant lift jointly
when they agree on the exact intersection. In particular, every lower
boundary-zero invariant lifts to a higher boundary-zero invariant.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineFiniteEtaleBoundaryKernelTransition
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {D' A' : Scheme.{0}} [IsAffine A'] (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  [IsClosedImmersion a] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : J.comap a = I)
set_option quotPrecheck false
local notation "β" => relationPullback p q (pullback.snd p J.subschemeι)
  (InvariantIdealRelation.snd J p q hJ) J.subschemeι (pullback.fst p J.subschemeι)
  pullback.condition (InvariantIdealRelation.snd_ι J p q hJ).symm

include hf e hJ hI in
/-- Prescribed lower coefficients and full higher boundary values lift simultaneously. -/
theorem exists_prescribed_lift (x : compatibleFunctions p' q')
    (y : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (hxy : I.subschemeι.appTop x.val =
      (IdealSheafClosedTransitions.map I J a hI).appTop y.val) :
    ∃ z : compatibleFunctions p q,
      relationPullback p q p' q' a b H.w hq z = x ∧ β z = y := by
  let _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  exact AffineFiniteEtaleSimultaneousLifting.exists_lift p q f hf e
    p' q' a b H hq _ _ J.subschemeι (pullback.fst p J.subschemeι)
    (IsPullback.of_hasPullback p J.subschemeι)
    (InvariantIdealRelation.snd_ι J p q hJ).symm
    I.subschemeι (IdealSheafClosedTransitions.map I J a hI)
    (IdealSheafClosedTransitions.isPullback I J a hI) x y hxy

include hf e hJ hI in
/-- The invariant order map is surjective on the entire exact boundary kernel. -/
theorem exists_boundary_zero_lift (x : compatibleFunctions p' q')
    (hx : I.subschemeι.appTop x.val = 0) :
    ∃ z : compatibleFunctions p q,
      relationPullback p q p' q' a b H.w hq z = x ∧ J.subschemeι.appTop z.val = 0 := by
  obtain ⟨z, hz, hb⟩ := exists_prescribed_lift p q f hf e p' q' a b H hq J hJ I hI x 0
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hx)
  exact ⟨z, hz, congrArg Subtype.val hb⟩

end FLT.Mazur.AffineFiniteEtaleBoundaryKernelTransition
