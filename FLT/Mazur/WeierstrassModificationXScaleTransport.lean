/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Transport of the full initial chart across an equal scale

A sealed single-coefficient transport preserves every original coordinate.
This avoids expanding unrelated coefficient casts in tensor comparisons.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s s' b3 b4 b6 : R)
  (hs : s = s')

/-- Transport the initial algebra across equality of its scale alone. -/
irreducible_def initialScaleTransportEquiv :
    Coordinate W s b3 b4 b6 ≃ₐ[R] Coordinate W s' b3 b4 b6 := by
  subst s'
  exact AlgEquiv.refl

/-- Scale transport preserves the incidence generator. -/
theorem initialScaleTransportEquiv_t :
    initialScaleTransportEquiv W s s' b3 b4 b6 hs (t W s b3 b4 b6) = t W s' b3 b4 b6 := by
  rw [initialScaleTransportEquiv_def]
  subst s'
  rfl

/-- Scale transport preserves the original slope. -/
theorem initialScaleTransportEquiv_v :
    initialScaleTransportEquiv W s s' b3 b4 b6 hs (v W s b3 b4 b6) = v W s' b3 b4 b6 := by
  rw [initialScaleTransportEquiv_def]
  subst s'
  rfl

/-- Scale transport preserves the entire original horizontal function. -/
theorem initialScaleTransportEquiv_x :
    initialScaleTransportEquiv W s s' b3 b4 b6 hs (x W s b3 b4 b6) = x W s' b3 b4 b6 := by
  rw [initialScaleTransportEquiv_def]
  subst s'
  rfl

/-- Scale transport preserves the entire original vertical function. -/
theorem initialScaleTransportEquiv_y :
    initialScaleTransportEquiv W s s' b3 b4 b6 hs (y W s b3 b4 b6) = y W s' b3 b4 b6 := by
  rw [initialScaleTransportEquiv_def]
  subst s'
  rfl

end FLT.Mazur.WeierstrassModificationX
