/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantLocalizationComparison

/-!
# Coordinates of the invariant localization comparison

The comparison with localized invariants sends each original invariant
numerator to its actual localization. Composing it with the fixed-ring
inclusion is exactly the localization of the original invariant inclusion.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  (r : invariantRing G A)

attribute [local instance] localizedAction

/-- Localize the original coordinate inclusion at a fixed denominator. -/
def localizedInclusion : Localization.Away r →+* Localization.Away (r : A) :=
  IsLocalization.Away.lift r
    (g := (algebraMap A (Localization.Away (r : A))).comp (inclusion G A))
    (IsLocalization.Away.algebraMap_isUnit (r : A))

/-- The fixed-ring comparison retains every original invariant numerator. -/
theorem canonicalInvariantLocalizationEquiv_algebraMap (a : invariantRing G A) :
    ((canonicalInvariantLocalizationEquiv G A r
      (algebraMap (invariantRing G A) (Localization.Away r) a) :
        invariantRing G (Localization.Away (r : A))) : Localization.Away (r : A)) =
      algebraMap A (Localization.Away (r : A)) (a : A) := by
  let _ := (invariantLocalizationMap G A (Localization.Away (r : A))
    (localizedAction_smul G A r)).toAlgebra
  exact congrArg Subtype.val ((invariantLocalizationEquiv G A (Localization.Away (r : A))
    (localizedAction_smul G A r) r).commutes a)

/-- The abstract comparison followed by inclusion equals the actual localized coordinate map. -/
theorem inclusion_comp_canonicalInvariantLocalizationEquiv :
    (inclusion G (Localization.Away (r : A))).comp
      (canonicalInvariantLocalizationEquiv G A r).toRingHom = localizedInclusion G A r := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext a
  change ((canonicalInvariantLocalizationEquiv G A r
    (algebraMap (invariantRing G A) (Localization.Away r) a) :
      invariantRing G (Localization.Away (r : A))) : Localization.Away (r : A)) = _
  rw [canonicalInvariantLocalizationEquiv_algebraMap]
  symm
  simp only [localizedInclusion, IsLocalization.Away.lift_eq, RingHom.comp_apply, inclusion,
    Subring.subtype_apply]

end FLT.Mazur.FiniteGroupQuotient
