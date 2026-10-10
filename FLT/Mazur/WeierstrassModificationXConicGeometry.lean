/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The smooth conic scheme and its actual rational neighborhoods

The conic structure morphism is smooth. Its two original principal opens
cover, and each is explicitly isomorphic to the same parameter-line open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The structure morphism of the original conic. -/
def conicStructure : Spec (.of (ConicCoordinate a c)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ConicCoordinate a c)))

/-- The original conic is smooth as a scheme over the coefficient ring. -/
theorem conicStructure_smooth (ha : IsUnit a) : Smooth (conicStructure a c) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (conicCoordinate_smooth a c ha)

/-- The first actual tangent open of the conic scheme. -/
def conicFirstOpenImmersion : Spec (.of (ConicFirstOpen a c)) ⟶
    Spec (.of (ConicCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ConicCoordinate a c) (ConicFirstOpen a c)))

/-- The second actual tangent open of the conic scheme. -/
def conicSecondOpenImmersion : Spec (.of (ConicSecondOpen a c)) ⟶
    Spec (.of (ConicCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ConicCoordinate a c) (ConicSecondOpen a c)))

instance conicFirstOpenImmersion_isOpenImmersion : IsOpenImmersion (conicFirstOpenImmersion a c) :=
  IsOpenImmersion.of_isLocalization (conicV a c + algebraMap R _ a)

instance conicSecondOpenImmersion_isOpenImmersion :
    IsOpenImmersion (conicSecondOpenImmersion a c) :=
  IsOpenImmersion.of_isLocalization (conicV a c)

/-- The first actual tangent neighborhood is isomorphic to the parameter open. -/
def conicFirstParameterIso (ha : IsUnit a) :
    Spec (.of (ConicFirstOpen a c)) ≅ Spec (.of (ConicParameterOpen c)) :=
  Scheme.Spec.mapIso (conicFirstParameterEquiv a c ha).toRingEquiv.toCommRingCatIso.op

/-- The second actual tangent neighborhood is isomorphic to the parameter open. -/
def conicSecondParameterIso (ha : IsUnit a) :
    Spec (.of (ConicSecondOpen a c)) ≅ Spec (.of (ConicParameterOpen c)) :=
  Scheme.Spec.mapIso (conicSecondParameterEquiv a c ha).toRingEquiv.toCommRingCatIso.op

/-- The first neighborhood has exactly the original tangent principal-open image. -/
theorem range_conicFirstOpenImmersion : Set.range (conicFirstOpenImmersion a c) =
    (PrimeSpectrum.basicOpen (conicV a c + algebraMap R _ a) :
      Set (PrimeSpectrum (ConicCoordinate a c))) :=
  PrimeSpectrum.localization_away_comap_range _ (conicV a c + algebraMap R _ a)

/-- The second neighborhood has exactly the other original tangent principal-open image. -/
theorem range_conicSecondOpenImmersion : Set.range (conicSecondOpenImmersion a c) =
    (PrimeSpectrum.basicOpen (conicV a c) : Set (PrimeSpectrum (ConicCoordinate a c))) :=
  PrimeSpectrum.localization_away_comap_range _ (conicV a c)

/-- The two actual rational neighborhoods cover the entire conic scheme. -/
theorem conicOpenImmersions_cover (ha : IsUnit a) (p : Spec (.of (ConicCoordinate a c))) :
    p ∈ Set.range (conicFirstOpenImmersion a c) ∨
      p ∈ Set.range (conicSecondOpenImmersion a c) := by
  rw [range_conicFirstOpenImmersion, range_conicSecondOpenImmersion]
  exact conic_tangent_opens_cover a c ha p

end FLT.Mazur.WeierstrassModificationX
