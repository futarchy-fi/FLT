/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueCastFactorization
/-!
# Evaluation of the original extended coefficient casts

Varying the target coefficients makes equality elimination preserve the exact
source type of the original cast. Its incidence and slope evaluations then
follow without unfolding the tensor algebra or losing the constant coefficient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX
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

/-- Coefficient transport preserves incidence evaluation. -/
theorem extendedCoefficientCast_t
    (e : Coordinate (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6) ≃ₐ[S] B) :
    extendedCoefficientCast W s b3 b4 b6 s' b3' b4' hs h3 h4 e
      (t (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (t (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6)) := by
  subst s'; subst b3'; subst b4'
  rfl

/-- Coefficient transport preserves slope evaluation. -/
theorem extendedCoefficientCast_v
    (e : Coordinate (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6) ≃ₐ[S] B) :
    extendedCoefficientCast W s b3 b4 b6 s' b3' b4' hs h3 h4 e
      (v (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (v (W.map (algebraMap R S)) s' b3' b4' (algebraMap R S b6)) := by
  subst s'; subst b3'; subst b4'
  rfl

/-- The original three-zero cast is the variable-target construction at zero. -/
theorem zeroExtendedCoefficientsEquiv_eq_general
    (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
    (h4 : algebraMap R S b4 = 0)
    (e : Coordinate (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6) ≃ₐ[S] B) :
    zeroExtendedCoefficientsEquiv W s b3 b4 b6 hs h3 h4 e =
      extendedCoefficientCast W s b3 b4 b6 0 0 0 hs h3 h4 e := rfl

/-- The original zero-coefficient cast preserves the incidence generator. -/
theorem zeroExtendedCoefficientsEquiv_t
    (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
    (h4 : algebraMap R S b4 = 0)
    (e : Coordinate (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6) ≃ₐ[S] B) :
    zeroExtendedCoefficientsEquiv W s b3 b4 b6 hs h3 h4 e
      (t (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (t (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6)) := by
  rw [zeroExtendedCoefficientsEquiv_eq_general, extendedCoefficientCast_t]
/-- The original zero-coefficient cast preserves the slope generator. -/
theorem zeroExtendedCoefficientsEquiv_v
    (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
    (h4 : algebraMap R S b4 = 0)
    (e : Coordinate (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6) ≃ₐ[S] B) :
    zeroExtendedCoefficientsEquiv W s b3 b4 b6 hs h3 h4 e
      (v (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    e (v (W.map (algebraMap R S)) 0 0 0 (algebraMap R S b6)) := by
  rw [zeroExtendedCoefficientsEquiv_eq_general, extendedCoefficientCast_v]
end FLT.Mazur.WeierstrassModificationX
