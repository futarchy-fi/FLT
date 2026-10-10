/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupAffineQuotient
public import FLT.Mazur.InvariantLocalizationCoordinates

/-!
# Principal charts of affine finite-group quotients

The quotient of an invariant principal open is the corresponding principal
open in the quotient. The comparison identifies the actual morphisms from
the localized source, not just the abstract rings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u

variable (G A : Type u) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  (r : invariantRing G A)

attribute [local instance] localizedAction

/-- The quotient of the principal localization is the localized quotient spectrum. -/
def principalQuotientIso :
    affineQuotient G (Localization.Away (r : A)) ≅ Spec (.of (Localization.Away r)) :=
  Scheme.Spec.mapIso (canonicalInvariantLocalizationEquiv G A r).toCommRingCatIso.op

/-- The comparison retains the actual quotient morphism on the localized source. -/
theorem quotientMap_principalQuotientIso :
    quotientMap G (Localization.Away (r : A)) ≫ (principalQuotientIso G A r).hom =
      Spec.map (CommRingCat.ofHom (localizedInclusion G A r)) := by
  change Spec.map (CommRingCat.ofHom (inclusion G (Localization.Away (r : A)))) ≫
    Spec.map (CommRingCat.ofHom (canonicalInvariantLocalizationEquiv G A r).toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (inclusion_comp_canonicalInvariantLocalizationEquiv G A r)

/-- Identify the localized quotient with the actual open subscheme in the original quotient. -/
def principalQuotientOpenIso :
    affineQuotient G (Localization.Away (r : A)) ≅
      Scheme.Opens.toScheme (X := affineQuotient G A) (PrimeSpectrum.basicOpen r) :=
  principalQuotientIso G A r ≪≫ (basicOpenIsoSpecAway (R := .of (invariantRing G A)) r).symm

omit [Finite G] in
/-- The localized quotient square commutes over the original affine quotient. -/
theorem localizedInclusion_square :
    Spec.map (CommRingCat.ofHom (localizedInclusion G A r)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (invariantRing G A) (Localization.Away r))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r : A)))) ≫
        quotientMap G A := by
  rw [quotientMap, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  change localizedInclusion G A r
    (algebraMap (invariantRing G A) (Localization.Away r) a) =
      algebraMap A (Localization.Away (r : A)) (inclusion G A a)
  simp only [localizedInclusion, IsLocalization.Away.lift_eq, RingHom.comp_apply]

end FLT.Mazur.FiniteGroupQuotient
