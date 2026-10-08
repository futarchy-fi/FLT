/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Cartesian squares of principal affine opens

Localizing an arbitrary ring map at an element and its image gives the actual
pullback square of principal open subschemes. This also applies to the
surjections from finite-relation models to their limiting rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PrincipalLocalizationSquare

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Inclusion of the principal affine open defined by an element. -/
def inclusion (r : A) : Spec (.of (Localization.Away r)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))

/-- Principal affine opens are open subschemes. -/
instance inclusion_isOpenImmersion (r : A) : IsOpenImmersion (inclusion r) := by
  dsimp [inclusion]
  infer_instance

/-- The inclusion has precisely the intended basic open as its image. -/
theorem inclusion_opensRange (r : A) : (inclusion r).opensRange =
    PrimeSpectrum.basicOpen r :=
  Scheme.Hom.opensRange_localizationAway (R := .of A) r

/-- Restriction of a spectrum morphism to corresponding principal opens. -/
def restriction (f : A →+* B) (r : A) :
    Spec (.of (Localization.Away (f r))) ⟶ Spec (.of (Localization.Away r)) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (Localization.Away r) (Localization.Away (f r)) f r))

/-- Localized ring maps commute with the open inclusions. -/
theorem condition (f : A →+* B) (r : A) :
    inclusion (f r) ≫ Spec.map (CommRingCat.ofHom f) = restriction f r ≫ inclusion r := by
  simp only [inclusion, restriction, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  simp [IsLocalization.Away.map]

/-- Principal localization gives a cartesian square, without flatness assumptions on the map. -/
theorem isPullback (f : A →+* B) (r : A) :
    IsPullback (restriction f r) (inclusion (f r)) (inclusion r)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (condition f r)
  rw [inclusion_opensRange, inclusion_opensRange]
  exact PrimeSpectrum.comap_basicOpen f r

end FLT.Mazur.PrincipalLocalizationSquare
