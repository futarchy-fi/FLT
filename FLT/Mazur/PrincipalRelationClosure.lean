/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationRelationClosure
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Coefficient closure on principal and iterated principal opens

The coefficient map is the actual localization map. A second denominator may
be any element of the first coefficient localization, including a fraction.
Both relation ideals are forced by the same ambient finite closure.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.NoetherianRelationContraction

universe u v

variable {P₀ : Type u} [CommRing P₀] {P : Type v} [CommRing P]
  (c : P₀ →+* P) (r : P₀)

/-- The canonical coefficient map on a principal open. -/
def principalCoefficientMap : Localization.Away r →+* Localization.Away (c r) :=
  IsLocalization.Away.map _ _ c r

/-- The coefficient map commutes with the actual principal localization maps. -/
theorem principalCoefficientMap_comp :
    (principalCoefficientMap c r).comp (algebraMap P₀ (Localization.Away r)) =
      (algebraMap P (Localization.Away (c r))).comp c := by
  unfold principalCoefficientMap IsLocalization.Away.map
  exact IsLocalization.map_comp _

/-- The principal-open relation ideal is the localization of the ambient closure. -/
theorem relations_principal (I : Ideal P) :
    relations (principalCoefficientMap c r)
        (I.map (algebraMap P (Localization.Away (c r)))) =
      (relations c I).map (algebraMap P (Localization.Away (c r))) := by
  apply relations_localization (Submonoid.powers r) (Submonoid.powers (c r)) c
    (principalCoefficientMap c r) (principalCoefficientMap_comp c r)
  exact Submonoid.map_powers c r

/-- Principal coefficient maps preserve injectivity, even when the denominator is a zero divisor. -/
theorem principalCoefficientMap_injective (hc : Function.Injective c) :
    Function.Injective (principalCoefficientMap c r) := by
  exact IsLocalization.map_injective_of_injective (Submonoid.powers r)
    (Localization.Away r) (Localization.Away (c r)) hc

/-- The second coefficient localization uses the literal transported denominator. -/
def iteratedCoefficientMap (s : Localization.Away r) :
    Localization.Away s →+* Localization.Away (principalCoefficientMap c r s) :=
  principalCoefficientMap (principalCoefficientMap c r) s

/-- Two localization steps retain exactly the same ambient finite relation ideal. -/
theorem relations_iterated (I : Ideal P) (s : Localization.Away r) :
    relations (iteratedCoefficientMap c r s)
        ((I.map (algebraMap P (Localization.Away (c r)))).map
          (algebraMap (Localization.Away (c r))
            (Localization.Away (principalCoefficientMap c r s)))) =
      ((relations c I).map (algebraMap P (Localization.Away (c r)))).map
        (algebraMap (Localization.Away (c r))
          (Localization.Away (principalCoefficientMap c r s))) := by
  rw [iteratedCoefficientMap, relations_principal, relations_principal]

/-- The iterated ideal is finite without a Noetherian hypothesis on the original base. -/
theorem relations_iterated_fg [IsNoetherianRing P₀] (I : Ideal P)
    (s : Localization.Away r) :
    (relations (iteratedCoefficientMap c r s)
      ((I.map (algebraMap P (Localization.Away (c r)))).map
        (algebraMap (Localization.Away (c r))
          (Localization.Away (principalCoefficientMap c r s))))).FG := by
  rw [relations_iterated]
  exact ((relations_fg c I).map _).map _

end FLT.Mazur.NoetherianRelationContraction
