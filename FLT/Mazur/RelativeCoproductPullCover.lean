/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCoproductComponentPullback

/-!
# The component open cover of an arbitrary map into a disjoint union

The inverse images of the components cover the entire original test. Arbitrary
relative morphisms on these pairwise disjoint opens glue uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {ι : Type u} {S : Scheme.{u}} (B : ι → Over S)
  {U : Over S} (k : U ⟶ relativeCoproductTest B)

/-- The actual inverse-image open cover, allowing more than one nonempty component. -/
def relativeCoproductPullCover : U.left.OpenCover :=
  (sigmaOpenCover (fun i ↦ (B i).left)).pullback₁ k.left

/-- A component inverse image with its original structure map. -/
def relativeCoproductPullTest (i : ι) : Over S :=
  Over.mk ((relativeCoproductPullCover B k).f i ≫ U.hom)

/-- The open component inverse image maps into the original domain. -/
def relativeCoproductPullToDomain (i : ι) : relativeCoproductPullTest B k i ⟶ U :=
  Over.homMk ((relativeCoproductPullCover B k).f i) rfl

/-- Its map to the original component is the genuine pullback projection. -/
def relativeCoproductPullToComponent (i : ι) : relativeCoproductPullTest B k i ⟶ B i :=
  Over.homMk (pullback.snd k.left (Sigma.ι (fun j ↦ (B j).left) i)) (by
    change pullback.snd _ _ ≫ (B i).hom = pullback.fst _ _ ≫ U.hom
    rw [← Over.w k, ← Category.assoc, pullback.condition, Category.assoc]
    change _ = pullback.snd _ _ ≫ Sigma.ι (fun j ↦ (B j).left) i ≫
      Sigma.desc (fun j ↦ (B j).hom)
    rw [Sigma.ι_comp_desc])

/-- The two original projections commute. -/
theorem relativeCoproductPull_square (i : ι) :
    relativeCoproductPullToDomain B k i ≫ k =
      relativeCoproductPullToComponent B k i ≫ relativeCoproductArrow B i :=
  Over.OverMorphism.ext pullback.condition

/-- Relative maps are determined on all actual component inverse images. -/
theorem relativeCoproductPull_hom_ext {V : Over S} {a b : U ⟶ V}
    (h : ∀ i, relativeCoproductPullToDomain B k i ≫ a =
      relativeCoproductPullToDomain B k i ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  exact (relativeCoproductPullCover B k).hom_ext _ _
    (fun i ↦ congrArg (fun z ↦ z.left) (h i))

/-- Different pulled-back components have empty intersections. -/
theorem relativeCoproductPull_intersection_empty {i j : ι} (hij : i ≠ j) :
    IsEmpty ↑(Limits.pullback ((relativeCoproductPullCover B k).f i)
      ((relativeCoproductPullCover B k).f j)) := by
  apply isEmpty_of_commSq_sigmaι_of_ne (g := fun i ↦ (B i).left) (i := i) (j := j)
    (a := pullback.fst _ _ ≫ (relativeCoproductPullToComponent B k i).left)
    (b := pullback.snd _ _ ≫ (relativeCoproductPullToComponent B k j).left) _ hij
  constructor
  have hi := congrArg (fun z ↦ z.left) (relativeCoproductPull_square B k i)
  have hj := congrArg (fun z ↦ z.left) (relativeCoproductPull_square B k j)
  change (relativeCoproductPullCover B k).f i ≫ k.left =
    (relativeCoproductPullToComponent B k i).left ≫ Sigma.ι (fun j ↦ (B j).left) i at hi
  change (relativeCoproductPullCover B k).f j ≫ k.left =
    (relativeCoproductPullToComponent B k j).left ≫ Sigma.ι (fun j ↦ (B j).left) j at hj
  change (pullback.fst _ _ ≫ _) ≫ _ = (pullback.snd _ _ ≫ _) ≫ _
  rw [Category.assoc, ← hi, Category.assoc, ← hj, pullback.condition_assoc]

/-- Arbitrary maps on the disjoint component inverse images are compatible. -/
theorem relativeCoproductPull_compatible {V : Over S}
    (g : ∀ i, relativeCoproductPullTest B k i ⟶ V) (i j : ι) :
    pullback.fst ((relativeCoproductPullCover B k).f i)
      ((relativeCoproductPullCover B k).f j) ≫ (g i).left =
        pullback.snd _ _ ≫ (g j).left := by
  by_cases hij : i = j
  · subst j
    have he : pullback.fst ((relativeCoproductPullCover B k).f i)
        ((relativeCoproductPullCover B k).f i) = pullback.snd _ _ :=
      (cancel_mono _).mp pullback.condition
    rw [he]
  · let _ := relativeCoproductPull_intersection_empty B k hij
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Actual relative morphisms glue across every component inverse image. -/
def relativeCoproductPullGlue {V : Over S}
    (g : ∀ i, relativeCoproductPullTest B k i ⟶ V) : U ⟶ V :=
  Over.homMk ((relativeCoproductPullCover B k).glueMorphisms
    (fun i ↦ (g i).left) (relativeCoproductPull_compatible B k g)) (by
      apply (relativeCoproductPullCover B k).hom_ext
      intro i
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
      exact Over.w (g i))

/-- Gluing restricts to precisely the supplied relative morphism on each open. -/
theorem relativeCoproductPullGlue_map {V : Over S}
    (g : ∀ i, relativeCoproductPullTest B k i ⟶ V) (i : ι) :
    relativeCoproductPullToDomain B k i ≫ relativeCoproductPullGlue B k g = g i :=
by
  apply Over.OverMorphism.ext
  change (relativeCoproductPullCover B k).f i ≫
    (relativeCoproductPullCover B k).glueMorphisms
      (fun j ↦ (g j).left) (relativeCoproductPull_compatible B k g) = (g i).left
  exact (relativeCoproductPullCover B k).ι_glueMorphisms
    (fun j ↦ (g j).left) (relativeCoproductPull_compatible B k g) i

end FLT.Mazur.SchemePicard
