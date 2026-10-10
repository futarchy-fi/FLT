/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYTripleOverlap
public import FLT.Mazur.WeierstrassModificationYIntersection

/-!
# Compatibility of the two y-chart maps to the modification

On D(r*u), the horizontal map factors through the actual x/divided overlap.
The coordinate factorization and the pushout relation prove equality of maps
to the modification itself, without assuming its contraction is a monomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The scale unit restricted to the common ratio open. -/
def intersectionScaleUnit : (RatioIntersection W s b3 b4 b6)ˣ :=
  (scaleUnit W s b3 b4 b6).map (intersectionScale W s b3 b4 b6).toMonoidHom

/-- The horizontal unit restricted to the common ratio open. -/
def intersectionHorizontalUnit : (RatioIntersection W s b3 b4 b6)ˣ :=
  (horizontalUnit W s b3 b4 b6).map (intersectionHorizontal W s b3 b4 b6).toMonoidHom

/-- The restricted scale unit is the actual scale coordinate. -/
theorem intersectionScaleUnit_val :
    (↑(intersectionScaleUnit W s b3 b4 b6) : RatioIntersection W s b3 b4 b6) =
      algebraMap _ _ (coord W s b3 b4 b6 0) := by
  change intersectionScale W s b3 b4 b6 (↑(scaleUnit W s b3 b4 b6)) = _
  rw [scaleUnit_val, intersectionScale_base]

/-- The restricted horizontal unit is the actual horizontal coordinate. -/
theorem intersectionHorizontalUnit_val :
    (↑(intersectionHorizontalUnit W s b3 b4 b6) : RatioIntersection W s b3 b4 b6) =
      algebraMap _ _ (coord W s b3 b4 b6 1) := by
  change intersectionHorizontal W s b3 b4 b6 (↑(horizontalUnit W s b3 b4 b6)) = _
  rw [horizontalUnit_val, intersectionHorizontal_base]

/-- The common ratio open maps to the actual x/divided overlap. -/
def intersectionToXOpen : Spec (.of (RatioIntersection W s b3 b4 b6)) ⟶
    Spec (.of (WeierstrassModificationX.XOpen W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (toXOpen W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
    (intersectionScaleUnit W s b3 b4 b6) (intersectionHorizontalUnit W s b3 b4 b6)
    (intersectionScaleUnit_val W s b3 b4 b6).symm
    (intersectionHorizontalUnit_val W s b3 b4 b6).symm).toRingHom)

/-- The factorization recovers the horizontal-open map to the x chart. -/
theorem intersectionToXOpen_toX :
    intersectionToXOpen W s b3 b4 b6 ≫ WeierstrassModificationX.xOpenInclusion W s b3 b4 b6 =
      intersectionToHorizontal W s b3 b4 b6 ≫ horizontalToX W s b3 b4 b6 := by
  rw [horizontalToX_eq]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change toXOpen W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
    (intersectionScaleUnit W s b3 b4 b6) (intersectionHorizontalUnit W s b3 b4 b6)
    (intersectionScaleUnit_val W s b3 b4 b6).symm
    (intersectionHorizontalUnit_val W s b3 b4 b6).symm (algebraMap _ _ z) =
    intersectionHorizontal W s b3 b4 b6 (toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm z)
  rw [toXOpen_base]
  have he : (intersectionHorizontal W s b3 b4 b6).comp
      (toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm) =
      toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (intersectionHorizontalUnit W s b3 b4 b6)
        (intersectionHorizontalUnit_val W s b3 b4 b6).symm := by
    apply WeierstrassModificationX.hom_ext
    · simp only [AlgHom.comp_apply, toX_t, map_mul]
      change intersectionHorizontal W s b3 b4 b6 (algebraMap _ _
        (coord W s b3 b4 b6 0)) * _ = _
      rw [intersectionHorizontal_base]
      rfl
    · simp only [AlgHom.comp_apply, toX_v]
      rfl
  exact (AlgHom.congr_fun he z).symm

/-- The same factorization recovers the scale-open map to the divided chart. -/
theorem intersectionToXOpen_toDivided :
    intersectionToXOpen W s b3 b4 b6 ≫
        WeierstrassModificationX.overlapToDivided W s b3 b4 b6 =
      intersectionToScale W s b3 b4 b6 ≫ scaleToDivided W s b3 b4 b6 := by
  rw [scaleToDivided_eq]
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change toXOpen W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
    (intersectionScaleUnit W s b3 b4 b6) (intersectionHorizontalUnit W s b3 b4 b6)
    (intersectionScaleUnit_val W s b3 b4 b6).symm
    (intersectionHorizontalUnit_val W s b3 b4 b6).symm
    (WeierstrassModificationX.overlapForward W s b3 b4 b6 (algebraMap _ _ z)) =
      intersectionScale W s b3 b4 b6 (toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (scaleUnit W s b3 b4 b6) (scaleUnit_val W s b3 b4 b6).symm z)
  rw [WeierstrassModificationX.overlapForward_base]
  have ht := AlgHom.congr_fun (toXOpen_dividedToXOpen W s b3 b4 b6
    (IsScalarTower.toAlgHom R _ _) (intersectionScaleUnit W s b3 b4 b6)
    (intersectionHorizontalUnit W s b3 b4 b6) (intersectionScaleUnit_val W s b3 b4 b6).symm
    (intersectionHorizontalUnit_val W s b3 b4 b6).symm) z
  refine ht.trans ?_
  have he : (intersectionScale W s b3 b4 b6).comp
      (toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (scaleUnit W s b3 b4 b6) (scaleUnit_val W s b3 b4 b6).symm) =
      toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (intersectionScaleUnit W s b3 b4 b6)
        (intersectionScaleUnit_val W s b3 b4 b6).symm := by
    apply WeierstrassDilatation.hom_ext
    · simp only [AlgHom.comp_apply, toDivided_x, map_mul]
      change intersectionScale W s b3 b4 b6 (algebraMap _ _
        (coord W s b3 b4 b6 1)) * _ = _
      rw [intersectionScale_base]
      rfl
    · simp only [AlgHom.comp_apply, toDivided_y]
      rfl
  exact (AlgHom.congr_fun he z).symm

/-- The actual y-chart maps agree on their scheme-theoretic intersection. -/
theorem ratioIntersection_compatibility :
    intersectionToScale W s b3 b4 b6 ≫ scaleToModification W s b3 b4 b6 =
      intersectionToHorizontal W s b3 b4 b6 ≫ horizontalToModification W s b3 b4 b6 := by
  rw [scaleToModification, horizontalToModification, ← Category.assoc, ← Category.assoc,
    ← intersectionToXOpen_toDivided, ← intersectionToXOpen_toX, Category.assoc, Category.assoc,
    WeierstrassModificationX.chart_overlap]

end FLT.Mazur.WeierstrassModificationY
