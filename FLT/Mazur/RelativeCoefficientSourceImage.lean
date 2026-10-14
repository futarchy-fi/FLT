/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCoefficientSourceCartesian
public import FLT.Mazur.SchemeEtaleImageQuotient

/-!
# Full coefficient images under surjective relative source changes

If the relative source comparison is surjective, the changed coefficient
image is the entire inverse image of the old image. For Cartesian translation
changes it suffices that the relative translation map be surjective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeCoefficientBaseChange
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme} (a : S' ⟶ S) {A T : Over S} {B : Over S'}
  (u : (Over.map a).obj B ⟶ A) (w : A ⟶ T)

/-- The base-changed coefficient map has exactly the full inverse image of the old range. -/
theorem baseMap_range : Set.range (baseMap a w).left =
    (toOld a (T := T)).left ⁻¹' Set.range w.left := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(toOld a (T := A)).left x,
      (congrArg (fun g ↦ g x) (baseMap_toOld a w)).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback (baseMap_isPullback a w) x y hx
    exact ⟨z, hz⟩

/-- A surjective relative source refinement retains every point of the changed old image. -/
theorem projection_range_of_relative_surjective
    [Surjective (projection a u (𝟙 A)).left] :
    Set.range (projection a u w).left =
      (toOld a (T := T)).left ⁻¹' Set.range w.left := by
  rw [projection_factor, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp]
  rw [Set.range_comp, Set.range_eq_univ.mpr
    (inferInstance : Surjective (projection a u (𝟙 A)).left).1, Set.image_univ]
  exact baseMap_range a w

/-- Every compatible old source and new ground point lifts to the complete source. -/
theorem relativeSource_exists_point [Surjective (projection a u (𝟙 A)).left]
    (x : A.left) (y : S') (hxy : A.hom x = a y) :
    ∃ z : B.left, u.left z = x ∧ B.hom z = y := by
  obtain ⟨z, hx, hy⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback A.hom a) x y hxy
  obtain ⟨b, hb⟩ := (inferInstance : Surjective (projection a u (𝟙 A)).left).1 z
  refine ⟨b, ?_, ?_⟩
  · have he := congrArg (fun g ↦ g b)
      (congrArg Over.Hom.left (projection_toOld a u (𝟙 A)))
    change (toOld a (T := A)).left ((projection a u (𝟙 A)).left b) = u.left b at he
    rw [hb] at he
    exact he.symm.trans hx
  · have he := congrArg (fun g ↦ g b) (projection a u (𝟙 A)).w
    change (target a (T := A)).hom ((projection a u (𝟙 A)).left b) = B.hom b at he
    rw [hb] at he
    exact he.symm.trans hy

/-- This is equality of actual open subschemes, retaining all nilpotent structure. -/
theorem projection_image_of_relative_surjective
    [Etale (projection a u (𝟙 A)).left] [Surjective (projection a u (𝟙 A)).left]
    [Etale w.left] :
    let _ := projection_etale_of_relative a u w
    SchemeEtaleImageQuotient.image (projection a u w).left =
      (toOld a (T := T)).left ⁻¹ᵁ SchemeEtaleImageQuotient.image w.left := by
  let _ := projection_etale_of_relative a u w
  apply SetLike.coe_injective
  exact projection_range_of_relative_surjective a u w

variable {V : Over S} {W : Over S'} (b : B ⟶ W) (v : A ⟶ V)
  (t : (Over.map a).obj W ⟶ V) (H : IsPullback u.left b.left v.left t.left)

include H in
/-- A surjective relative translation gives a surjective comparison of the COMPLETE sources. -/
theorem relativeSource_surjective [Surjective (projection a t (𝟙 V)).left] :
    Surjective (projection a u (𝟙 A)).left :=
  MorphismProperty.of_isPullback (relativeSource_isPullback a u b v t H).flip
    (inferInstanceAs (Surjective (projection a t (𝟙 V)).left))

end FLT.Mazur.RelativeCoefficientBaseChange
