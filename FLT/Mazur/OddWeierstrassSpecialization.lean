/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralWeierstrassCharacteristicCover

/-!
# Specialization of the odd coefficient chart

Every smooth five-coefficient equation with three invertible specializes the
actual D(3) chart. The construction retains all coefficients and commutes with
arbitrary ring maps, including maps to characteristic two and nonreduced rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (SmoothRing OddChartRing oddChartEquation)
variable {R S : Type} [CommRing R] [CommRing S]

/-- Original smooth equations specialize the odd chart without inverting two. -/
def specialize (W : WeierstrassCurve R) (h₃ : IsUnit (3 : R)) (hΔ : IsUnit W.Δ) :
    OddChartRing →+* R :=
  IsLocalization.Away.lift (3 : SmoothRing)
    (show IsUnit (IntegralWeierstrassParameter.specialize W hΔ 3) by
      rw [map_ofNat]
      exact h₃)

/-- Specialization retains the discriminant-only coefficient map. -/
@[simp] theorem specialize_algebraMap (W : WeierstrassCurve R)
    (h₃ : IsUnit (3 : R)) (hΔ : IsUnit W.Δ) (a : SmoothRing) :
    specialize W h₃ hΔ (algebraMap SmoothRing OddChartRing a) =
      IntegralWeierstrassParameter.specialize W hΔ a :=
  IsLocalization.Away.lift_eq _ _ _

/-- The odd-chart equation recovers every original coefficient. -/
theorem oddChartEquation_specialize (W : WeierstrassCurve R)
    (h₃ : IsUnit (3 : R)) (hΔ : IsUnit W.Δ) :
    oddChartEquation.map (specialize W h₃ hΔ) = W := by
  rw [oddChartEquation, WeierstrassCurve.map_map]
  convert IntegralWeierstrassParameter.smoothEquation_specialize W hΔ using 2
  exact IsLocalization.Away.lift_comp _ _

/-- The odd-chart parameter is natural under arbitrary specialization of coefficients. -/
theorem specialize_natural (W : WeierstrassCurve R) (h₃ : IsUnit (3 : R))
    (hΔ : IsUnit W.Δ) (f : R →+* S) (h₃' : IsUnit (3 : S))
    (hΔ' : IsUnit (W.map f).Δ) :
    f.comp (specialize W h₃ hΔ) = specialize (W.map f) h₃' hΔ' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (3 : SmoothRing))
  apply RingHom.ext
  intro a
  simpa only [RingHom.comp_apply, specialize_algebraMap] using
    DFunLike.congr_fun (IntegralWeierstrassParameter.specialize_natural W hΔ f hΔ') a

end FLT.Mazur.OddWeierstrassParameter
