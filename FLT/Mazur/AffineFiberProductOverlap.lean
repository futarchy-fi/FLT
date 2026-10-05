/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricOverlap
public import FLT.Mazur.AffineModuleGlobalSections

/-!
# Exact overlap normalization on the categorical fiber product

Pullback along the canonical tensor-spectrum chart is fully faithful.
Conjugating by the two projection comparisons therefore gives an exact
bijection between actual fiber-product overlaps and tensor-chart overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules)

/-- Isomorphisms between the actual categorical fiber-product projection pullbacks. -/
abbrev FiberProductOverlap :=
  (pullback (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M ≅
  (pullback (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M

local instance : (pullback (pullbackSpecIso R S S).inv).Full :=
  inferInstanceAs (AffineModuleGlobalSections.pullbackEquivalence
    (pullbackSpecIso R S S).symm).functor.Full
local instance : (pullback (pullbackSpecIso R S S).inv).Faithful :=
  inferInstanceAs (AffineModuleGlobalSections.pullbackEquivalence
    (pullbackSpecIso R S S).symm).functor.Faithful

/-- Recover the categorical fiber-product overlap from its tensor-spectrum chart. -/
def toFiberProduct (e : Overlap R S M) : FiberProductOverlap R S M :=
  (pullback (pullbackSpecIso R S S).inv).preimageIso
    (firstProjectionIso R S M ≪≫ e ≪≫ (secondProjectionIso R S M).symm)

/-- The reconstructed categorical overlap has the required chart conjugation. -/
theorem toFiberProduct_mapIso (e : Overlap R S M) :
    (pullback (pullbackSpecIso R S S).inv).mapIso (toFiberProduct R S M e) =
      firstProjectionIso R S M ≪≫ e ≪≫ (secondProjectionIso R S M).symm := by
  apply Iso.ext
  exact Functor.map_preimage _ _

/-- Normalizing a reconstructed categorical overlap returns the original chart overlap. -/
theorem fromFiberProduct_toFiberProduct (e : Overlap R S M) :
    fromFiberProduct R S M (toFiberProduct R S M e) = e := by
  unfold fromFiberProduct
  rw [toFiberProduct_mapIso]
  simp

/-- Tensor-spectrum normalization detects equality of categorical overlaps. -/
theorem fromFiberProduct_injective : Function.Injective (fromFiberProduct R S M) := by
  intro e f h
  apply Iso.ext
  apply (pullback (pullbackSpecIso R S S).inv).map_injective
  have hh := congrArg Iso.hom h
  change (firstProjectionIso R S M).inv ≫ _ ≫ (secondProjectionIso R S M).hom =
    (firstProjectionIso R S M).inv ≫ _ ≫ (secondProjectionIso R S M).hom at hh
  exact (cancel_mono (secondProjectionIso R S M).hom).mp
    ((cancel_epi (firstProjectionIso R S M).inv).mp (by simpa only [Category.assoc, Functor.mapIso_hom] using hh))

/-- Reconstruction after normalization returns the original categorical overlap. -/
theorem toFiberProduct_fromFiberProduct (e : FiberProductOverlap R S M) :
    toFiberProduct R S M (fromFiberProduct R S M e) = e :=
  fromFiberProduct_injective R S M (fromFiberProduct_toFiberProduct R S M _)

/-- Actual categorical overlaps and their tensor charts are exactly equivalent. -/
def fiberProductEquiv : FiberProductOverlap R S M ≃ Overlap R S M where
  toFun := fromFiberProduct R S M
  invFun := toFiberProduct R S M
  left_inv := toFiberProduct_fromFiberProduct R S M
  right_inv := fromFiberProduct_toFiberProduct R S M

end FLT.Mazur.AffineGeometricOverlap
