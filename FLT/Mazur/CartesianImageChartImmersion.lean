/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion
public import FLT.Mazur.ClosedImmersionCartesianCover
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Immersions from cartesian closed charts covering the image

An open family need only cover the image of a morphism. If its full pullbacks
are closed immersions, the morphism is closed into the union of those opens,
and hence is an immersion into the original target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur
universe u v
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v} {V : ι → Scheme.{u}}
  (j : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ i, f x ∈ Set.range (j i))

/-- Restrict the original morphism to the union of the actual target chart images. -/
def imageChartFactor : X ⟶ (openImageUnion j).toScheme :=
  IsOpenImmersion.lift (openImageUnion j).ι f (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr (hc x))

/-- The factorization preserves the original morphism to its original target. -/
theorem imageChartFactor_ι : imageChartFactor f j hc ≫ (openImageUnion j).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

variable (A : ι → Scheme.{u}) (p : ∀ i, A i ⟶ X) (q : ∀ i, A i ⟶ V i)
  (H : ∀ i, IsPullback (p i) (q i) f (j i))

include H in
/-- Restricting the target to the chart union retains the original cartesian chart squares. -/
theorem imageChartFactor_isPullback (i : ι) :
    IsPullback (p i) (q i) (imageChartFactor f j hc) (openImageUnionMap j i) := by
  have he : p i ≫ imageChartFactor f j hc = q i ≫ openImageUnionMap j i := by
    apply (cancel_mono (openImageUnion j).ι).mp
    rw [Category.assoc, Category.assoc, imageChartFactor_ι, openImageUnionMap_fac]
    exact (H i).w
  have hz (z : PullbackCone (imageChartFactor f j hc) (openImageUnionMap j i)) :
      z.fst ≫ f = z.snd ≫ j i := by
    have h := congrArg (· ≫ (openImageUnion j).ι) z.condition
    simpa only [Category.assoc, imageChartFactor_ι, openImageUnionMap_fac] using h
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk he
    (fun z ↦ (H i).lift z.fst z.snd (hz z))
    (fun z ↦ (H i).lift_fst _ _ _) (fun z ↦ (H i).lift_snd _ _ _)
    (fun z k hk hq ↦ (H i).hom_ext
      (hk.trans ((H i).lift_fst _ _ _).symm) (hq.trans ((H i).lift_snd _ _ _).symm)))

include H in
/-- Closedness on full cartesian charts makes the factor into their union closed. -/
theorem imageChartFactor_isClosedImmersion (hq : ∀ i, IsClosedImmersion (q i)) :
    IsClosedImmersion (imageChartFactor f j hc) :=
  isClosedImmersion_of_cartesian_cover _ (openImageUnionCover j) A p q
    (imageChartFactor_isPullback f j hc A p q H) hq

include hc H in
/-- A morphism with closed full pullbacks on an image-covering open family is an immersion. -/
theorem isImmersion_of_cartesian_image_charts (hq : ∀ i, IsClosedImmersion (q i)) :
    IsImmersion f := by
  let _ := imageChartFactor_isClosedImmersion f j hc A p q H hq
  rw [← imageChartFactor_ι f j hc]
  infer_instance

end FLT.Mazur
