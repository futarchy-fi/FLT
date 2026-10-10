/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberSecondNode
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

variable {R : Type*} [CommRing R] (a : R)

/-- The actual inclusion of the first fiber neighborhood. -/
def firstFiberOpenImmersion : Spec (.of (FirstFiberOpen a)) ⟶
    Spec (.of (FiberCoordinate a 0)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiberCoordinate a 0) (FirstFiberOpen a)))

/-- The actual inclusion of the second fiber neighborhood. -/
def secondFiberOpenImmersion : Spec (.of (SecondFiberOpen a)) ⟶
    Spec (.of (FiberCoordinate a 0)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiberCoordinate a 0) (SecondFiberOpen a)))

instance firstFiberOpenImmersion_isOpenImmersion :
    IsOpenImmersion (firstFiberOpenImmersion a) :=
  IsOpenImmersion.of_isLocalization (fiberV a 0 + algebraMap R _ a)

instance secondFiberOpenImmersion_isOpenImmersion :
    IsOpenImmersion (secondFiberOpenImmersion a) :=
  IsOpenImmersion.of_isLocalization (fiberV a 0)

/-- The first node comparison is an actual scheme isomorphism. -/
def firstNodeIso : Spec (.of (FirstNodeOpen a)) ≅ Spec (.of (FirstFiberOpen a)) :=
  Scheme.Spec.mapIso (firstNodeEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The second node comparison is an actual scheme isomorphism. -/
def secondNodeIso : Spec (.of (FirstNodeOpen (-a))) ≅ Spec (.of (SecondFiberOpen a)) :=
  Scheme.Spec.mapIso (secondNodeEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The first oriented node chart of the entire fiber. -/
def firstNodeChart : Spec (.of (FirstNodeOpen a)) ⟶ Spec (.of (FiberCoordinate a 0)) :=
  (firstNodeIso a).hom ≫ firstFiberOpenImmersion a

/-- The second oriented node chart of the entire fiber. -/
def secondNodeChart : Spec (.of (FirstNodeOpen (-a))) ⟶ Spec (.of (FiberCoordinate a 0)) :=
  (secondNodeIso a).hom ≫ secondFiberOpenImmersion a

instance firstNodeChart_isOpenImmersion : IsOpenImmersion (firstNodeChart a) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance secondNodeChart_isOpenImmersion : IsOpenImmersion (secondNodeChart a) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The first node chart has precisely the original principal-open image. -/
theorem range_firstNodeChart : Set.range (firstNodeChart a) =
    (PrimeSpectrum.basicOpen (fiberV a 0 + algebraMap R _ a) :
      Set (PrimeSpectrum (FiberCoordinate a 0))) := by
  have h : Set.range (firstNodeChart a) = Set.range (firstFiberOpenImmersion a) :=
    by
      change Set.range (fun z ↦ firstFiberOpenImmersion a ((firstNodeIso a).hom z)) = _
      simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
        (firstNodeIso a).hom.homeomorph.surjective.range_comp (firstFiberOpenImmersion a)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range _ (fiberV a 0 + algebraMap R _ a)

/-- The second node chart has precisely the other original principal-open image. -/
theorem range_secondNodeChart : Set.range (secondNodeChart a) =
    (PrimeSpectrum.basicOpen (fiberV a 0) : Set (PrimeSpectrum (FiberCoordinate a 0))) := by
  have h : Set.range (secondNodeChart a) = Set.range (secondFiberOpenImmersion a) :=
    by
      change Set.range (fun z ↦ secondFiberOpenImmersion a ((secondNodeIso a).hom z)) = _
      simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
        (secondNodeIso a).hom.homeomorph.surjective.range_comp (secondFiberOpenImmersion a)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range _ (fiberV a 0)

/-- The two actual open node charts jointly cover the complete three-line scheme. -/
theorem nodeCharts_cover (ha : IsUnit a) (p : Spec (.of (FiberCoordinate a 0))) :
    p ∈ Set.range (firstNodeChart a) ∨ p ∈ Set.range (secondNodeChart a) := by
  rw [range_firstNodeChart, range_secondNodeChart]
  exact fiber_node_opens_cover a ha p

end FLT.Mazur.WeierstrassModificationX
