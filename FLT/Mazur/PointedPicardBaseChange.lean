/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedPicardNormalization
public import FLT.Mazur.RelativePicardPresheaf

/-!
# Pointed Picard kernels under change of test scheme

The section of each actual fiber product commutes with its restriction maps.
Consequently pullback preserves the kernel, and normalization is natural.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The chosen section on the actual total space of a test scheme. -/
def pointedBaseSection (T : Over S) : T.left ⟶ Limits.pullback f T.hom :=
  Limits.pullback.lift (T.hom ≫ e) (𝟙 T.left)
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

/-- The fiber-product section splits its second projection. -/
@[reassoc (attr := simp)]
theorem pointedBaseSection_snd (T : Over S) :
    pointedBaseSection f e he T ≫ Limits.pullback.snd f T.hom = 𝟙 T.left :=
  Limits.pullback.lift_snd _ _ _

/-- The first projection of the fiber-product section is the original section. -/
@[reassoc (attr := simp)]
theorem pointedBaseSection_fst (T : Over S) :
    pointedBaseSection f e he T ≫ Limits.pullback.fst f T.hom = T.hom ≫ e :=
  Limits.pullback.lift_fst _ _ _

/-- The actual sections commute with restriction along a map of test schemes. -/
@[reassoc]
theorem pointedBaseSection_naturality {T U : Over S} (g : T ⟶ U) :
    pointedBaseSection f e he T ≫ relativeTotalMap f g =
      g.left ≫ pointedBaseSection f e he U := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, relativeTotalMap_fst, pointedBaseSection_fst]
    rw [← Category.assoc, Over.w g]
  · simp

/-- Restriction to the chosen section commutes with Picard pullback. -/
theorem pointedBaseSection_pullback {T U : Over S} (g : T ⟶ U)
    (a : Pic (Limits.pullback f U.hom)) :
    pullback (pointedBaseSection f e he T) (pullback (relativeTotalMap f g) a) =
      pullback g.left (pullback (pointedBaseSection f e he U) a) := by
  rw [← pullback_comp, pointedBaseSection_naturality, pullback_comp]

/-- Normalizing a line-bundle class commutes with change of test scheme. -/
theorem normalize_baseMap {T U : Over S} (g : T ⟶ U)
    (a : Pic (Limits.pullback f U.hom)) :
    normalize (Limits.pullback.snd f T.hom) (pointedBaseSection f e he T)
        (pullback (relativeTotalMap f g) a) =
      pullback (relativeTotalMap f g)
        (normalize (Limits.pullback.snd f U.hom) (pointedBaseSection f e he U) a) := by
  simp only [normalize_apply, map_div, pointedBaseSection_pullback]
  rw [← pullback_comp (relativeTotalMap f g), relativeTotalMap_snd, pullback_comp]

/-- Restriction on the subgroup of classes trivial at the section. -/
def pointedKernelMap {T U : Over S} (g : T ⟶ U) :
    (pullback (pointedBaseSection f e he U)).ker →*
      (pullback (pointedBaseSection f e he T)).ker where
  toFun a := ⟨pullback (relativeTotalMap f g) a.val, by
    change pullback (pointedBaseSection f e he T) _ = 1
    rw [pointedBaseSection_pullback, a.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

/-- The kernel restriction retains the original Picard pullback. -/
@[simp]
theorem pointedKernelMap_val {T U : Over S} (g : T ⟶ U)
    (a : (pullback (pointedBaseSection f e he U)).ker) :
    (pointedKernelMap f e he g a).val = pullback (relativeTotalMap f g) a.val := rfl

end FLT.Mazur.SchemePicard
