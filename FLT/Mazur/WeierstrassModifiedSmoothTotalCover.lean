/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModifiedSmoothOutputCoordinates

/-!
# Complete affine input and output refinement of a modified smooth product

An actual affine cover of a modified curve induces a cover of its entire
product with the original smooth locus. Refine every such product by all
original output charts and then by affine opens. The resulting source cover
retains the original parameter, contracted input and actual addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  {Y : Scheme.{u}} (c : Y ⟶ integralCurve W) (C : Y.AffineOpenCover)
  (d : ∀ i : C.I₀, Spec (C.X i) ⟶ integralCurve W)
  (hd : ∀ i, C.f i ≫ c = d i)

/-- The product uses the original smooth locus and the entire modified curve. -/
abbrev modifiedSmoothProduct :=
  pullback (integralSmoothStructure W) (c ≫ integralCurveStructure W)

/-- Pull the actual affine input cover back along the second projection. -/
def modifiedSmoothInputProductCover : (modifiedSmoothProduct W c).OpenCover :=
  Scheme.Pullback.openCoverOfRight C.openCover
    (integralSmoothStructure W) (c ≫ integralCurveStructure W)

/-- A member of the pulled-back input cover is the actual affine smooth-input product. -/
def modifiedSmoothInputProductIso (i : C.I₀) :
    (modifiedSmoothInputProductCover W c C).X i ≅
      modifiedSmoothAffineProduct W (d i) :=
  pullback.congrHom rfl ((Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ integralCurveStructure W) (hd i)))

/-- The actual affine-input product as an open of the full product. -/
def modifiedSmoothInputMap (i : C.I₀) :
    modifiedSmoothAffineProduct W (d i) ⟶ modifiedSmoothProduct W c :=
  (modifiedSmoothInputProductIso W c C d hd i).inv ≫ (modifiedSmoothInputProductCover W c C).f i

instance modifiedSmoothInputMap_isOpenImmersion (i : C.I₀) :
    IsOpenImmersion (modifiedSmoothInputMap W c C d hd i) := by
  unfold modifiedSmoothInputMap
  infer_instance

/-- The cover with the actual affine-input products as its named members. -/
def modifiedSmoothInputCover : (modifiedSmoothProduct W c).OpenCover :=
  (modifiedSmoothInputProductCover W c C).copy C.I₀
    (fun i => modifiedSmoothAffineProduct W (d i))
    (modifiedSmoothInputMap W c C d hd) (Equiv.refl _)
    (fun i => (modifiedSmoothInputProductIso W c C d hd i).symm) (fun _ => rfl)

/-- Refine every input member by its entire affine output cover. -/
def modifiedSmoothTotalOpenCover : (modifiedSmoothProduct W c).OpenCover :=
  (modifiedSmoothInputCover W c C d hd).bind
    (fun i => (modifiedSmoothAffineCover W (d i)).openCover)

/-- The entire modified smooth product has actual affine input and output presentations. -/
def modifiedSmoothTotalCover : (modifiedSmoothProduct W c).AffineOpenCover where
  I₀ := (i : C.I₀) × (modifiedSmoothAffineCover W (d i)).I₀
  X i := (modifiedSmoothAffineCover W (d i.1)).X i.2
  f i := (modifiedSmoothAffineCover W (d i.1)).f i.2 ≫
    modifiedSmoothInputMap W c C d hd i.1
  idx z := (modifiedSmoothTotalOpenCover W c C d hd).idx z
  covers z := (modifiedSmoothTotalOpenCover W c C d hd).covers z

/-- A refined input member retains the original smooth parameter. -/
@[reassoc] theorem modifiedSmoothInputMap_fst (i : C.I₀) :
    modifiedSmoothInputMap W c C d hd i ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [modifiedSmoothInputMap, modifiedSmoothInputProductIso,
    modifiedSmoothInputProductCover, Scheme.Pullback.openCoverOfRight_f,
    Category.assoc, Category.comp_id, pullback.congrHom_inv,
    pullback.map, pullback.lift_fst]
  exact pullback.lift_fst _ _ _

/-- A refined input member retains the original modified second point. -/
@[reassoc] theorem modifiedSmoothInputMap_snd (i : C.I₀) :
    modifiedSmoothInputMap W c C d hd i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ C.f i := by
  simp only [modifiedSmoothInputMap, modifiedSmoothInputProductIso,
    modifiedSmoothInputProductCover, Scheme.Pullback.openCoverOfRight_f,
    Category.assoc, pullback.congrHom_inv, pullback.map,
    pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
    Scheme.AffineOpenCover.openCover_f]

/-- The whole product carries its actual original contracted action. -/
def modifiedSmoothAddition : modifiedSmoothProduct W c ⟶ integralCurve W :=
  leftSmoothPointAddition W (pullback.fst _ _) (pullback.snd _ _ ≫ c)
    (by rw [Category.assoc]; exact pullback.condition)

/-- Restricting the original action to an input chart gives its constructed affine-input action. -/
@[reassoc] theorem modifiedSmoothInputMap_addition (i : C.I₀) :
    modifiedSmoothInputMap W c C d hd i ≫ modifiedSmoothAddition W c =
      modifiedSmoothAffineAddition W (d i) := by
  unfold modifiedSmoothAddition modifiedSmoothAffineAddition leftSmoothPointAddition
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, modifiedSmoothInputMap_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, modifiedSmoothInputMap_snd_assoc,
      pullback.lift_snd, hd]

/-- Every actual affine presentation retains the original whole-product action. -/
@[reassoc] theorem modifiedSmoothTotalCover_addition
    (i : (modifiedSmoothTotalCover W c C d hd).I₀) :
    (modifiedSmoothTotalCover W c C d hd).f i ≫ modifiedSmoothAddition W c =
      (modifiedSmoothAffineCover W (d i.1)).f i.2 ≫
        modifiedSmoothAffineAddition W (d i.1) := by
  change (_ ≫ modifiedSmoothInputMap W c C d hd i.1) ≫ _ = _
  rw [Category.assoc, modifiedSmoothInputMap_addition]

end FLT.Mazur.WeierstrassIntegralChart
