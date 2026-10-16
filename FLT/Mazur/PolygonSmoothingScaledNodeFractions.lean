/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingScaledNodePolynomials
public import FLT.Mazur.LocalizationJointRestriction
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The original reciprocal action on localized node functions

The induced localization map carries any retained numerator equation to its
literal coefficient-and-variable substitution, on the matching scaled open.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (t : R) (s : S) (hs : f t = s) (a : Sˣ)
local notation "F" => scaledNodeRingMap f t s hs a
local notation "d" => nodeMarkingDenominator t

/-- The original node neighborhood pulled back along the full reciprocal action. -/
abbrev ScaledNodeLocalization := Localization.Away ((F) (d))

/-- The actual ring restriction into the scaled original node neighborhood. -/
def scaledNodeLocalizationMap :
    Localization.Away (d) →+* ScaledNodeLocalization f t s hs a :=
  LocalizationJointRestriction.restriction (F) (d)

/-- This restriction retains the full original chart ring map on every numerator. -/
theorem scaledNodeLocalizationMap_algebraMap (b : ChartRing t) :
    scaledNodeLocalizationMap f t s hs a (algebraMap (ChartRing t) _ b) =
      algebraMap (ChartRing s) (ScaledNodeLocalization f t s hs a) ((F) b) :=
  LocalizationJointRestriction.restriction_algebraMap (F) (d) b

/-- A retained polynomial numerator is transformed by literal reciprocal substitution. -/
theorem scaledNodeLocalizationMap_polynomial (p : MvPolynomial (Fin 2) R) :
    scaledNodeLocalizationMap f t s hs a (nodeLocalizedPolynomialMap t p) =
      algebraMap (ChartRing s) (ScaledNodeLocalization f t s hs a)
        (Ideal.Quotient.mk (relationIdeal s) (scaledNodePolynomialMap f a p)) := by
  rw [nodeLocalizedPolynomialMap, RingHom.comp_apply,
    scaledNodeLocalizationMap_algebraMap, scaledNodePolynomialMap_mk]

/-- The exact original numerator equation survives with its actual scaled denominator. -/
theorem scaledNodeLocalizationMap_numerator
    (v : Localization.Away (d)) (r : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : v * algebraMap (ChartRing t) _ (d) ^ r = nodeLocalizedPolynomialMap t p) :
    scaledNodeLocalizationMap f t s hs a v *
        algebraMap (ChartRing s) (ScaledNodeLocalization f t s hs a) ((F) (d)) ^ r =
      algebraMap (ChartRing s) (ScaledNodeLocalization f t s hs a)
        (Ideal.Quotient.mk (relationIdeal s) (scaledNodePolynomialMap f a p)) := by
  have he := congrArg (scaledNodeLocalizationMap f t s hs a) hp
  simpa only [map_mul, map_pow, scaledNodeLocalizationMap_algebraMap,
    scaledNodeLocalizationMap_polynomial] using he

/-- The localized action commutes with the actual original affine chart maps. -/
theorem scaledNodeLocalizationMap_spec :
    AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (scaledNodeLocalizationMap f t s hs a)) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (ChartRing t) (Localization.Away (d)))) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (ChartRing s) (ScaledNodeLocalization f t s hs a))) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (F)) := by
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  apply congrArg AlgebraicGeometry.Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (scaledNodeLocalizationMap_algebraMap f t s hs a)

end FLT.Mazur.PolygonSmoothing
