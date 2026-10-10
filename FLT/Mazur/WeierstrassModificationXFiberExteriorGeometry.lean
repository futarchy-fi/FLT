/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberExteriorSlope
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The full punctured slope boundary with both original restriction maps

The same punctured slope chart parametrizes both the horizontal and infinity
boundaries of the full fiber. The two localization comparisons commute with
every original fiber function, and the chart factors through the incidence line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "F" => FiberCoordinate a c
local notation "q" => fiberConicFactor a c
local notation "v" => fiberV a c
local notation "O" => Localization.Away q
local notation "Y" => Localization.Away (q * v)
local notation "P" => SlopeOpen a

/-- The entire punctured slope line is the original horizontal principal spectrum. -/
def fiberExteriorSlopeIso : Spec (.of P) ≅ Spec (.of O) :=
  Scheme.Spec.mapIso (fiberExteriorSlopeEquiv a c).toRingEquiv.toCommRingCatIso.op

/-- The punctured slope chart in the complete original fiber. -/
def fiberExteriorSlopeChart :=
  (fiberExteriorSlopeIso a c).hom ≫ PrincipalOpenTransport.inclusion q

instance fiberExteriorSlopeChart_isOpenImmersion :
    IsOpenImmersion (fiberExteriorSlopeChart a c) := inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The slope chart covers precisely the full original horizontal boundary. -/
theorem fiberExteriorSlopeChart_range : Set.range (fiberExteriorSlopeChart a c) =
    (PrimeSpectrum.basicOpen q : Set (PrimeSpectrum F)) :=
  PrincipalOpenTransport.chart_range q (fiberExteriorSlopeEquiv a c)

/-- The original infinity and horizontal localizations are isomorphic over the whole fiber. -/
def fiberExteriorInfinityIso : Spec (.of O) ≅ Spec (.of Y) :=
  IsOpenImmersion.isoOfRangeEq (PrincipalOpenTransport.inclusion q)
    (PrincipalOpenTransport.inclusion (q * v)) (by
      change Set.range (PrimeSpectrum.comap (algebraMap F O)) =
        Set.range (PrimeSpectrum.comap (algebraMap F Y))
      rw [PrimeSpectrum.localization_away_comap_range _ q,
        PrimeSpectrum.localization_away_comap_range _ (q * v), fiberExterior_infinity_open])

/-- The horizontal-to-infinity comparison retains restriction of every original fiber function. -/
@[reassoc] theorem fiberExteriorInfinityIso_inclusion :
    (fiberExteriorInfinityIso a c).hom ≫ PrincipalOpenTransport.inclusion (q * v) =
      PrincipalOpenTransport.inclusion q := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The full punctured slope line also parametrizes the original infinity localization. -/
def fiberInfinitySlopeIso : Spec (.of P) ≅ Spec (.of Y) :=
  fiberExteriorSlopeIso a c ≪≫ fiberExteriorInfinityIso a c

/-- The infinity parameterization retains the same original full-fiber inclusion. -/
@[reassoc] theorem fiberInfinitySlopeIso_inclusion :
    (fiberInfinitySlopeIso a c).hom ≫ PrincipalOpenTransport.inclusion (q * v) =
      fiberExteriorSlopeChart a c := by
  rw [fiberInfinitySlopeIso, Iso.trans_hom, Category.assoc, fiberExteriorInfinityIso_inclusion]
  rfl

/-- The full exterior parametrization is the original incidence-line restriction. -/
@[reassoc] theorem fiberExteriorSlopeChart_incidence :
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) P)) ≫
      fiberIncidenceImmersion a c = fiberExteriorSlopeChart a c := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun z => (fiberExteriorSlopeEquiv_base a c z).symm)

end FLT.Mazur.WeierstrassModificationX
