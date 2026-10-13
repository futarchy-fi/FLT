/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCyclicMarking
public import FLT.Mazur.PolygonCompleteMarkingCartier

/-!
# The original finite cyclic markings in the actual smooth locus

Every chosen complete-family square retains the original smooth sections.
Their finite etale carrier embeds in the actual smooth open, with the same
closed map into the whole family and the same labeled sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

include hs in
/-- The specified cartesian structure map is locally finitely presented. -/
theorem completeCartesianProjection_lfp : LocallyOfFinitePresentation q := by
  let _ := exactVeroneseProjToBase_lfp K n h
  exact MorphismProperty.of_isPullback hs inferInstance

attribute [local instance] exactVeroneseProjToBase_lfp
variable [LocallyOfFinitePresentation q]

include hs in
/-- The smooth open is the inverse image of the original complete smooth open. -/
theorem completeCartesian_preimage_smoothLocus :
    p ⁻¹ᵁ (exactVeroneseProjToBase K n h).smoothLocus = q.smoothLocus := by
  let _ := exactVeroneseProjToBase_flat K n h
  rw [← hs.isoPullback_hom_fst, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_smoothLocus_baseChange, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact hs.isoPullback_hom_snd

/-- Each original labeled marking lies in the actual smooth locus after any base change. -/
theorem completeCartesianMarking_range_smoothLocus (i : Fin n) :
    Set.range (completeCartesianMarking K n h s p q hs i) ⊆ (q.smoothLocus : Set Y) := by
  rw [← completeCartesian_preimage_smoothLocus K n h s p q hs]
  rintro _ ⟨x, rfl⟩
  change p (completeCartesianMarking K n h s p q hs i x) ∈
    (exactVeroneseProjToBase K n h).smoothLocus
  rw [← Scheme.Hom.comp_apply, completeCartesianMarking_fst, Scheme.Hom.comp_apply]
  exact completeBaseMarking_range_smoothLocus K n h i ⟨s x, rfl⟩

/-- The specified original section lifted to the actual smooth open. -/
def completeSmoothCartesianMarking (i : Fin n) :
    S ⟶ q.smoothLocus := by
  exact IsOpenImmersion.lift q.smoothLocus.ι (completeCartesianMarking K n h s p q hs i)
    (by simpa only [Scheme.Opens.range_ι] using
      completeCartesianMarking_range_smoothLocus K n h s p q hs i)

/-- Smooth lifting retains exactly the original marking in the whole family. -/
@[reassoc] theorem completeSmoothCartesianMarking_ι (i : Fin n) :
    completeSmoothCartesianMarking K n h s p q hs i ≫ q.smoothLocus.ι =
      completeCartesianMarking K n h s p q hs i := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- The full finite etale marking carrier in the actual relative smooth open. -/
def completeSmoothCyclicMarking :
    ConstantCyclicGroup.model S n ⟶ Over.mk (q.smoothLocus.ι ≫ q) := by
  exact Sigma.desc fun a ↦ Over.homMk
    (completeSmoothCartesianMarking K n h s p q hs ((ZMod.finEquiv n).symm a))
    (by
      change _ ≫ q.smoothLocus.ι ≫ q = 𝟙 S
      rw [← Category.assoc, completeSmoothCartesianMarking_ι,
      completeCartesianMarking_snd])

/-- The smooth finite marking map recovers the original whole-family embedding. -/
@[reassoc] theorem completeSmoothCyclicMarking_ι :
    (completeSmoothCyclicMarking K n h s p q hs).left ≫ q.smoothLocus.ι =
      (completeCyclicMarking K n h s p q hs).left := by
  have he : completeSmoothCyclicMarking K n h s p q hs ≫
      (Over.homMk q.smoothLocus.ι rfl :
        Over.mk (q.smoothLocus.ι ≫ q) ⟶ Over.mk q) =
          completeCyclicMarking K n h s p q hs := by
    apply Sigma.hom_ext
    intro a
    simp only [completeSmoothCyclicMarking, completeCyclicMarking,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    apply Over.OverMorphism.ext
    exact completeSmoothCartesianMarking_ι K n h s p q hs _
  exact congrArg Over.Hom.left he

/-- The finite marking carrier is closed even in the actual smooth open. -/
theorem completeSmoothCyclicMarking_closed :
    IsClosedImmersion (completeSmoothCyclicMarking K n h s p q hs).left := by
  let _ : IsClosedImmersion ((completeSmoothCyclicMarking K n h s p q hs).left ≫
      q.smoothLocus.ι) := by
    rw [completeSmoothCyclicMarking_ι]
    exact completeCyclicMarking_closed K n h s p q hs
  exact IsClosedImmersion.of_comp _ q.smoothLocus.ι

end FLT.Mazur.PolygonInfinitesimalStages
