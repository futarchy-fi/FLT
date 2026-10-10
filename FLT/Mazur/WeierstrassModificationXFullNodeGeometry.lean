/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullSecondNode
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# A scheme cover by the two actual node neighborhoods

The two principal-open comparisons give open immersions into the full fiber.
Their images cover when the original tangent difference is a unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)

/-- The actual inclusion of the first fiber neighborhood. -/
def fullFirstFiberOpenImmersion : Spec (.of (FullFirstFiberOpen a c)) ⟶
    Spec (.of (FiberCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiberCoordinate a c) (FullFirstFiberOpen a c)))

/-- The actual inclusion of the second fiber neighborhood. -/
def fullSecondFiberOpenImmersion : Spec (.of (FullSecondFiberOpen a c)) ⟶
    Spec (.of (FiberCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiberCoordinate a c) (FullSecondFiberOpen a c)))

instance fullFirstFiberOpenImmersion_isOpenImmersion :
    IsOpenImmersion (fullFirstFiberOpenImmersion a c) :=
  IsOpenImmersion.of_isLocalization (fiberV a c + algebraMap R _ a)

instance fullSecondFiberOpenImmersion_isOpenImmersion :
    IsOpenImmersion (fullSecondFiberOpenImmersion a c) :=
  IsOpenImmersion.of_isLocalization (fiberV a c)

/-- The first node comparison is an actual scheme isomorphism. -/
def fullFirstNodeIso : Spec (.of (FullNodeOpen a c)) ≅ Spec (.of (FullFirstFiberOpen a c)) :=
  Scheme.Spec.mapIso (fullFirstNodeEquiv a c ha).toRingEquiv.toCommRingCatIso.op

/-- The second node comparison is an actual scheme isomorphism. -/
def fullSecondNodeIso : Spec (.of (FullNodeOpen (-a) c)) ≅ Spec (.of (FullSecondFiberOpen a c)) :=
  Scheme.Spec.mapIso (fullSecondNodeEquiv a c ha).toRingEquiv.toCommRingCatIso.op

/-- The first oriented node chart of the entire fiber. -/
def fullFirstNodeChart : Spec (.of (FullNodeOpen a c)) ⟶ Spec (.of (FiberCoordinate a c)) :=
  (fullFirstNodeIso a c ha).hom ≫ fullFirstFiberOpenImmersion a c

/-- The second oriented node chart of the entire fiber. -/
def fullSecondNodeChart : Spec (.of (FullNodeOpen (-a) c)) ⟶ Spec (.of (FiberCoordinate a c)) :=
  (fullSecondNodeIso a c ha).hom ≫ fullSecondFiberOpenImmersion a c

instance fullFirstNodeChart_isOpenImmersion : IsOpenImmersion (fullFirstNodeChart a c ha) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance fullSecondNodeChart_isOpenImmersion : IsOpenImmersion (fullSecondNodeChart a c ha) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The first node chart has precisely the original principal-open image. -/
theorem range_fullFirstNodeChart : Set.range (fullFirstNodeChart a c ha) =
    (PrimeSpectrum.basicOpen (fiberV a c + algebraMap R _ a) :
      Set (PrimeSpectrum (FiberCoordinate a c))) := by
  have h : Set.range (fullFirstNodeChart a c ha) = Set.range (fullFirstFiberOpenImmersion a c) :=
    by
      change Set.range (fun z ↦
        fullFirstFiberOpenImmersion a c ((fullFirstNodeIso a c ha).hom z)) = _
      simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
        (fullFirstNodeIso a c ha).hom.homeomorph.surjective.range_comp
          (fullFirstFiberOpenImmersion a c)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range _ (fiberV a c + algebraMap R _ a)

/-- The second node chart has precisely the other original principal-open image. -/
theorem range_fullSecondNodeChart : Set.range (fullSecondNodeChart a c ha) =
    (PrimeSpectrum.basicOpen (fiberV a c) : Set (PrimeSpectrum (FiberCoordinate a c))) := by
  have h : Set.range (fullSecondNodeChart a c ha) = Set.range (fullSecondFiberOpenImmersion a c) :=
    by
      change Set.range (fun z ↦
        fullSecondFiberOpenImmersion a c ((fullSecondNodeIso a c ha).hom z)) = _
      simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
        (fullSecondNodeIso a c ha).hom.homeomorph.surjective.range_comp
          (fullSecondFiberOpenImmersion a c)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range _ (fiberV a c)

/-- The two actual open node charts jointly cover the complete full fiber scheme. -/
theorem fullNodeCharts_cover (p : Spec (.of (FiberCoordinate a c))) :
    p ∈ Set.range (fullFirstNodeChart a c ha) ∨ p ∈ Set.range (fullSecondNodeChart a c ha) := by
  rw [range_fullFirstNodeChart, range_fullSecondNodeChart]
  exact fullFiber_tangent_opens_cover a c ha p

end FLT.Mazur.WeierstrassModificationX
