/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalIntegerRestriction
public import FLT.Mazur.PrincipalTargetRestrictionIsomorphism

/-!
# Canonical algebra equivalences on principal target opens

A principal target open inside an affine open immersion's image gives an
algebra equivalence, including when its source denominator is named separately.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Explicitly identifying the denominator preserves canonical bijectivity. -/
theorem principalRestrictionAlgHom_bijective {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) (x : B) (y : C) (h : f x = y)
    (hb : Function.Bijective (LocalizationJointRestriction.restriction f.toRingHom x)) :
    Function.Bijective (principalRestrictionAlgHom f x y h) := by
  subst y
  change Function.Bijective (principalRestrictionAlgHom f x (f x) rfl).toRingHom
  rw [principalRestrictionAlgHom_toRingHom]
  exact hb

/-- An open immersion gives a canonical localized algebra equivalence on each
principal target open contained in its image. -/
def principalTargetAlgEquiv {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (x : B) (y : C) (h : f x = y)
    (hx : (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum B)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom f.toRingHom))) :
    Localization.Away x ≃ₐ[R] Localization.Away y :=
  AlgEquiv.ofBijective (principalRestrictionAlgHom f x y h)
    (principalRestrictionAlgHom_bijective f x y h
      (principalTargetRestriction_bijective f.toRingHom x hx))

/-- The equivalence retains the original algebra map on chart elements. -/
@[simp]
theorem principalTargetAlgEquiv_algebraMap {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (x : B) (y : C) (h : f x = y)
    (hx : (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum B)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom f.toRingHom))) (b : B) :
    principalTargetAlgEquiv f x y h hx (algebraMap B (Localization.Away x) b) =
      algebraMap C (Localization.Away y) (f b) :=
  principalRestrictionAlgHom_algebraMap f x y h b

/-- A chart-compatible equivalence certifies bijectivity of the canonical restriction. -/
theorem restriction_bijective_of_chart_equiv {B C : Type u}
    [CommRing B] [CommRing C] (f : B →+* C) (x : B)
    (e : Localization.Away x ≃+* Localization.Away (f x))
    (he : ∀ b, e (algebraMap B _ b) = algebraMap C _ (f b)) :
    Function.Bijective (LocalizationJointRestriction.restriction f x) := by
  have heq : LocalizationJointRestriction.restriction f x = e.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers x)
    ext b
    exact (LocalizationJointRestriction.restriction_algebraMap f x b).trans (he b).symm
  rw [heq]
  exact e.bijective

end FLT.Mazur.Approximation
