/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.OneGonTransition
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The one-gon overlap with the multiplicative chart

The punctured normalization maps openly to the Laurent chart with coordinate
z = t/(t-1). Its image is the complement of z = 1. This is the second leg
of the overlap needed to glue the one-gon node chart to the multiplicative chart.
-/

@[expose] public noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.OneGonTransition

variable (R : Type*) [CommRing R]

/-- The multiplicative chart with its point one removed. -/
abbrev torusPuncture :=
  Localization.Away (algebraMap R[X] R[T;T⁻¹] (X - 1))

/-- Successive localization at t and t-1 inverts their product. -/
instance torusPuncture_localization :
    IsLocalization.Away (X * (X - 1) : R[X]) (torusPuncture R) :=
  IsLocalization.Away.mul' R[T;T⁻¹] (torusPuncture R) X (X - 1)

/-- Identify the two presentations of the punctured affine line. -/
def localizationEquiv : puncture R ≃ₐ[R[X]] torusPuncture R :=
  IsLocalization.algEquiv (Submonoid.powers (X * (X - 1) : R[X])) _ _

/-- The ordinary Laurent coordinate restricts to the normalization coordinate. -/
def torusRestriction : R[T;T⁻¹] →+* puncture R :=
  (localizationEquiv R).symm.toRingHom.comp (algebraMap R[T;T⁻¹] (torusPuncture R))

@[simp]
theorem torusRestriction_T :
    torusRestriction R (LaurentPolynomial.T 1) = (coordinate R : puncture R) := by
  have h := (localizationEquiv R).symm.commutes X
  simpa [IsScalarTower.algebraMap_apply R[X] R[T;T⁻¹] (torusPuncture R),
    LaurentPolynomial.algebraMap_eq_toLaurent, torusRestriction] using h

/-- Pullback of Laurent functions under the actual overlap coordinate change. -/
def overlapMap : R[T;T⁻¹] →+* puncture R :=
  (transition R).toRingHom.comp (torusRestriction R)

@[simp]
theorem overlapMap_T : overlapMap R (LaurentPolynomial.T 1) = (mobius R : puncture R) := by
  change transition R (torusRestriction R _) = _
  rw [torusRestriction_T, transition_coordinate]

/-- The algebra involution as an isomorphism of the punctured scheme. -/
def transitionSpecIso : Spec (.of (puncture R)) ≅ Spec (.of (puncture R)) :=
  Scheme.Spec.mapIso (transitionEquiv R).toRingEquiv.toCommRingCatIso.op

/-- The two localization presentations as isomorphic schemes. -/
def localizationSpecIso : Spec (.of (puncture R)) ≅ Spec (.of (torusPuncture R)) :=
  Scheme.Spec.mapIso (localizationEquiv R).symm.toRingEquiv.toCommRingCatIso.op

/-- The standard principal open immersion into the multiplicative chart. -/
def torusOpen : Spec (.of (torusPuncture R)) ⟶ Spec (.of R[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (algebraMap R[T;T⁻¹] (torusPuncture R)))

instance torusOpen_isOpenImmersion : IsOpenImmersion (torusOpen R) :=
  IsOpenImmersion.of_isLocalization (algebraMap R[X] R[T;T⁻¹] (X - 1))

/-- The overlap immersion with the coordinate t/(t-1). -/
def toTorus : Spec (.of (puncture R)) ⟶ Spec (.of R[T;T⁻¹]) :=
  (transitionSpecIso R).hom ≫ (localizationSpecIso R).hom ≫ torusOpen R

theorem toTorus_eq_specMap :
    toTorus R = Spec.map (CommRingCat.ofHom (overlapMap R)) := by
  simp only [toTorus, overlapMap, torusRestriction, CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

instance toTorus_isOpenImmersion : IsOpenImmersion (toTorus R) := by
  dsimp [toTorus]
  infer_instance

/-- The principal open is the complement of the point with coordinate one. -/
theorem range_torusOpen : Set.range (torusOpen R) =
    (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : R[T;T⁻¹]) :
      Set (PrimeSpectrum R[T;T⁻¹])) := by
  have hc : algebraMap R[X] R[T;T⁻¹] (X - 1) =
      (LaurentPolynomial.T 1 - 1 : R[T;T⁻¹]) := by
    rw [map_sub, map_one, LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
  rw [← hc]
  exact PrimeSpectrum.localization_away_comap_range (torusPuncture R)
    (algebraMap R[X] R[T;T⁻¹] (X - 1))

/-- The coordinate change has image exactly the torus with one removed. -/
theorem range_toTorus : Set.range (toTorus R) =
    (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : R[T;T⁻¹]) :
      Set (PrimeSpectrum R[T;T⁻¹])) := by
  rw [← range_torusOpen]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(localizationSpecIso R).hom ((transitionSpecIso R).hom y), rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(transitionSpecIso R).inv ((localizationSpecIso R).inv y), ?_⟩
    change torusOpen R ((localizationSpecIso R).hom
      ((transitionSpecIso R).hom ((transitionSpecIso R).inv
        ((localizationSpecIso R).inv y)))) = torusOpen R y
    have ht := congrArg (fun f : Spec (.of (puncture R)) ⟶ Spec (.of (puncture R)) ↦
      f ((localizationSpecIso R).inv y)) (transitionSpecIso R).inv_hom_id
    have hl := congrArg (fun f : Spec (.of (torusPuncture R)) ⟶
      Spec (.of (torusPuncture R)) ↦ f y) (localizationSpecIso R).inv_hom_id
    change (transitionSpecIso R).hom ((transitionSpecIso R).inv _) =
      (localizationSpecIso R).inv y at ht
    change (localizationSpecIso R).hom ((localizationSpecIso R).inv y) = y at hl
    rw [ht, hl]

end FLT.Mazur.OneGonTransition
