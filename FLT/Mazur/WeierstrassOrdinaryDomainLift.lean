/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAffineUnits

/-!
# Lifting affine pairs to ordinary addition domains

The universal property of each denominator localization constructs an ordinary
chart specialization. In particular a reciprocal law with affine output lifts
to the matching ordinary chart without extending the coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Lift a pair to its chosen ordinary chart when its denominator is invertible. -/
def ordinaryDomainLift (b : Bool) (f : AffineProduct W →ₐ[R] S)
    (hf : IsUnit (f (if b then tangentDenominator W else secantDenominator W))) :
    additionChartRing W (ordinaryIndex b) →ₐ[R] S := by
  cases b with
  | false =>
    exact IsLocalization.Away.liftAlgHom (S := SecantChart W) (secantDenominator W) hf
  | true =>
    exact IsLocalization.Away.liftAlgHom (S := TangentChart W) (tangentDenominator W) hf

/-- The lift has exactly the original affine inputs. -/
theorem ordinaryDomainLift_restriction (b : Bool) (f : AffineProduct W →ₐ[R] S)
    (hf : IsUnit (f (if b then tangentDenominator W else secantDenominator W))) :
    (ordinaryDomainLift W b f hf).comp (additionChartAlgRestriction W (ordinaryIndex b)) =
      f := by
  ext a
  cases b
  · exact IsLocalization.Away.lift_eq (S := SecantChart W) (secantDenominator W) hf a
  · exact IsLocalization.Away.lift_eq (S := TangentChart W) (tangentDenominator W) hf a

/-- A reciprocal specialization with affine output also has an ordinary specialization. -/
def reciprocalAffineOrdinaryLift (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hz : IsUnit (f (reciprocalChartAddition W b (coord W 1 2)))) :
    additionChartRing W (ordinaryIndex b) →ₐ[R] S :=
  ordinaryDomainLift W b (f.comp (additionChartAlgRestriction W (reciprocalIndex b)))
    (reciprocalSpecialization_ordinary_unit W b f hz)

/-- Replacing the reciprocal chart by the ordinary chart preserves both inputs. -/
theorem reciprocalAffineOrdinaryLift_restriction (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hz : IsUnit (f (reciprocalChartAddition W b (coord W 1 2)))) :
    (reciprocalAffineOrdinaryLift W b f hz).comp
        (additionChartAlgRestriction W (ordinaryIndex b)) =
      f.comp (additionChartAlgRestriction W (reciprocalIndex b)) :=
  ordinaryDomainLift_restriction W b _ _

end FLT.Mazur.WeierstrassIntegralChart
