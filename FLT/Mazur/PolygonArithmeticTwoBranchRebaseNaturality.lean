/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchRebase

/-!
# Arithmetic quotient compatibility of the rebased terminal correction

Both the inverse scalar drift and the full rebased node factor commute with
the original coefficient restrictions, before passing to spectra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (π : R)

/-- Both scalar drift units use the original quotient map. -/
theorem twoBranchCorrectionDriftUnit_restriction (m : ℕ) (q : Bool → R[T;T⁻¹]) :
    Units.map (restriction R π m).toMonoidHom (twoBranchCorrectionDriftUnit R π (m + 1) q) =
      twoBranchCorrectionDriftUnit R π m q := by
  apply Units.ext
  change restriction R π m (↑(twoBranchCorrectionDriftUnit R π (m + 1) q)) =
    (twoBranchCorrectionDriftUnit R π m q : Quotient R π m)
  simp only [twoBranchCorrectionDriftUnit, Units.val_mul, map_mul,
    nilpotentMultiplier_val, map_add, map_one, restriction_parameter, AlgHom.commutes]

/-- The inverse common smoothing drift commutes with every arithmetic quotient. -/
theorem twoBranchCorrectionRebasedSmoothing_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : Bool → R[T;T⁻¹]) :
    restriction R π m (twoBranchCorrectionRebasedSmoothing R π (m + 1) t q) =
      twoBranchCorrectionRebasedSmoothing R π m s q := by
  have hi := congrArg (fun v : (Quotient R π m)ˣ ↦ (↑v⁻¹ : Quotient R π m))
    (twoBranchCorrectionDriftUnit_restriction R π m q)
  rw [← map_inv] at hi
  simp only [twoBranchCorrectionRebasedSmoothing, map_mul, hs]
  exact congrArg (fun z ↦ z * s) hi

/-- Identity coefficient identifications commute with an arbitrary coefficient arrow. -/
theorem correctionIdentification_square {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a a' : A) (b b' : B) (ha : a = a') (hb : b = b')
    (h : f a = b) (h' : f a' = b') :
    (ringMap f a' b' h').comp (nodeParameterEquiv a a' ha).toAlgHom.toRingHom =
      (nodeParameterEquiv b b' hb).toAlgHom.toRingHom.comp (ringMap f a b h) := by
  subst a'
  subst b'
  rw [nodeParameterEquiv_toRingHom, nodeParameterEquiv_toRingHom,
    ringMap_id, ringMap_id, RingHom.id_comp, RingHom.comp_id]

/-- The entire rebased correction follows the original quotient map on both coordinates. -/
theorem twoBranchCorrectionRebasedFactor_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : Bool → R[T;T⁻¹]) :
    (ringMap (restriction R π m).toRingHom
        (twoBranchCorrectionRebasedSmoothing R π (m + 1) t q)
        (twoBranchCorrectionRebasedSmoothing R π m s q)
        (twoBranchCorrectionRebasedSmoothing_restriction R π m t s hs q)).comp
      (twoBranchCorrectionRebasedFactor R π (m + 1) t q).toAlgHom.toRingHom =
    (twoBranchCorrectionRebasedFactor R π m s q).toAlgHom.toRingHom.comp
      (ringMap (restriction R π m).toRingHom t s hs) := by
  let a := twoBranchCorrectionRebasedSmoothing R π (m + 1) t q
  let b := twoBranchCorrectionRebasedSmoothing R π m s q
  have hab : restriction R π m a = b :=
    twoBranchCorrectionRebasedSmoothing_restriction R π m t s hs q
  rw [twoBranchCorrectionRebasedFactor_def, twoBranchCorrectionRebasedFactor_def]
  exact correctionCompose_square
    (ringMap (restriction R π m).toRingHom t s hs)
    (ringMap (restriction R π m).toRingHom
      (twoBranchCorrectionSmoothing R π (m + 1) a q) (twoBranchCorrectionSmoothing R π m b q)
      (twoBranchCorrectionSmoothing_restriction R π m a b hab q))
    (ringMap (restriction R π m).toRingHom a b hab) _ _ _ _
    (twoBranchCorrectionNodeFactor_restriction R π m a b hab q)
    (correctionIdentification_square _ _ _ _ _ _ _ _ _)

end FLT.Mazur.PolygonArithmeticStages
