/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantIdealRelationCoefficients

/-!
# Literal full boundary coefficient membership under exact ideal transport

Extract the endpoint equation before specializing to large named schemes.
No ring-homomorphism comparison is required at the specialization site.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.InvariantIdealRelationCoefficients
open SchemeEffectiveEpiSections
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (hp : b ≫ p = p' ≫ a) (hq : b ≫ q = q' ≫ a)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : I.comap p' = I.comap q') (hIJ : J.comap a = I)

include hp hq in
/-- The literal coefficient pullback satisfies both complete boundary endpoint equations. -/
theorem pullback_mem (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ)) :
    (IdealSheafClosedTransitions.map I J a hIJ).appTop t.val ∈
      compatibleFunctions (pullback.snd p' I.subschemeι)
        (InvariantIdealRelation.snd I p' q' hI) :=
  (restriction p q p' q' a b hp hq J hJ I hI hIJ t).property

end FLT.Mazur.InvariantIdealRelationCoefficients
