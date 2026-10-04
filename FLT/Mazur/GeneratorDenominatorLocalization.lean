/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationJointRestriction
public import FLT.Mazur.PrincipalLocalizationGeneration

/-!
# Localizing a chart at a proved generator denominator

A relation f(b) = x f(t) puts x in the image after both rings are localized
compatibly at t and f(t). The inverse of f(t) is also in this image.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GeneratorDenominatorLocalization
variable {K S R : Type*} [CommRing K] [CommRing S] [CommRing R]
  [Algebra K S] [Algebra K R]

/-- The compatible algebra map between the specified principal localizations. -/
def map (f : S →ₐ[K] R) (t : S) :
    Localization.Away t →ₐ[K] Localization.Away (f t) :=
  IsLocalization.Away.mapₐ (Localization.Away t) (Localization.Away (f t)) f t

/-- Restriction agrees with the original chart map on every numerator. -/
lemma map_algebraMap (f : S →ₐ[K] R) (t b : S) :
    map f t (algebraMap S (Localization.Away t) b) =
      algebraMap R (Localization.Away (f t)) (f b) := by
  exact LocalizationJointRestriction.restriction_algebraMap f.toRingHom t b

/-- The inverse of the chosen image denominator has its actual localized preimage. -/
lemma map_invSelf (f : S →ₐ[K] R) (t : S) :
    map f t (IsLocalization.Away.invSelf t) = IsLocalization.Away.invSelf (f t) := by
  exact LocalizationJointRestriction.restriction_invSelf f.toRingHom t

/-- A cross-multiplied generator identity gives an explicit image witness. -/
lemma generator_mem (f : S →ₐ[K] R) (t b : S) (x : R) (hx : x * f t = f b) :
    algebraMap R (Localization.Away (f t)) x ∈ (map f t).range := by
  refine ⟨algebraMap S (Localization.Away t) b * IsLocalization.Away.invSelf t, ?_⟩
  change map f t (algebraMap S (Localization.Away t) b * IsLocalization.Away.invSelf t) = _
  rw [map_mul, map_algebraMap, map_invSelf, ← hx, map_mul, mul_assoc,
    IsLocalization.Away.mul_invSelf, mul_one]

/-- Every original image remains in the localized image. -/
lemma image_mem (f : S →ₐ[K] R) (t b : S) :
    algebraMap R (Localization.Away (f t)) (f b) ∈ (map f t).range :=
  ⟨algebraMap S (Localization.Away t) b, map_algebraMap f t b⟩

/-- The denominator inverse is part of the image, not an implicit assumption. -/
lemma inverse_mem (f : S →ₐ[K] R) (t : S) :
    IsLocalization.Away.invSelf (f t) ∈ (map f t).range :=
  ⟨IsLocalization.Away.invSelf t, map_invSelf f t⟩

end FLT.Mazur.GeneratorDenominatorLocalization
