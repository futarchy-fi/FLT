/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueFiber
/-!
# Evaluation of the original extended coefficient casts

Varying the target coefficients makes equality elimination preserve the exact
source type of the original cast. Its horizontal coordinate and vertical coordinate evaluations then
follow without unfolding the tensor algebra or losing the constant coefficient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing B] [Algebra S B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (s' b3' b4' : S) (hs : algebraMap R S s = s')
  (h3 : algebraMap R S b3 = b3') (h4 : algebraMap R S b4 = b4')

/-- Transport to arbitrary equal target coefficients, retaining the extended source. -/
def extendedCoefficientCast
    (e : Coordinate (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6) ≃ₐ[S] B) :
    ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S] B := by
  change Coordinate _ _ _ _ _ ≃ₐ[_] _
  rw [hs, h3, h4]
  exact e

/-- Coefficient transport preserves horizontal coordinate evaluation. -/
theorem extendedCoefficientCast_x
    (e : Coordinate (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6) ≃ₐ[S] B) :
    extendedCoefficientCast W s b3 b4 b6 s' b3' b4' hs h3 h4 e
      (x (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (x (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6)) := by
  subst s'; subst b3'; subst b4'
  rfl

/-- Coefficient transport preserves vertical coordinate evaluation. -/
theorem extendedCoefficientCast_y
    (e : Coordinate (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6) ≃ₐ[S] B) :
    extendedCoefficientCast W s b3 b4 b6 s' b3' b4' hs h3 h4 e
      (y (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (y (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6)) := by
  subst s'; subst b3'; subst b4'
  rfl


end FLT.Mazur.WeierstrassDilatation
