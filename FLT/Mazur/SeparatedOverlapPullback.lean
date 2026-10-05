/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOpenCover

/-!
# Separatedness from specified overlap pullbacks

One may test the diagonal using any proved models of the actual chart
intersections. Closedness of their maps into the chart products assembles
into separatedness of the structural morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.SeparatedOpenCover

universe u v

/-- A closed overlap-product map makes the corresponding diagonal chart closed. -/
theorem closed_mapDesc_of_isPullback {X Y Z W S : Scheme.{u}}
    (f : X ⟶ S) (i : Y ⟶ X) (j : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) (hp : IsPullback a b i j)
    (hc : IsClosedImmersion
      (pullback.lift (f := i ≫ f) (g := j ≫ f) a b
        (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ f) hp.w))) :
    IsClosedImmersion (pullback.mapDesc i j f) := by
  have he : pullback.lift (f := i ≫ f) (g := j ≫ f) a b
      (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ f) hp.w) =
      hp.isoPullback.hom ≫ pullback.mapDesc i j f := by
    apply pullback.hom_ext <;> simp
  rw [he] at hc
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp hc

/-- Assemble separatedness from closed product maps of specified actual overlaps. -/
theorem of_overlap_pullbacks {X S : Scheme.{u}} (f : X ⟶ S) (U : X.OpenCover.{v})
    (W : U.I₀ → U.I₀ → Scheme.{u})
    (a : ∀ i j, W i j ⟶ U.X i) (b : ∀ i j, W i j ⟶ U.X j)
    (hp : ∀ i j, IsPullback (a i j) (b i j) (U.f i) (U.f j))
    (hc : ∀ i j, IsClosedImmersion (pullback.lift (f := U.f i ≫ f) (g := U.f j ≫ f) (a i j) (b i j)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ f) (hp i j).w))) :
    IsSeparated f :=
  of_pairwise f U fun i j ↦
    closed_mapDesc_of_isPullback f (U.f i) (U.f j) (a i j) (b i j) (hp i j) (hc i j)

end FLT.Mazur.SeparatedOpenCover
