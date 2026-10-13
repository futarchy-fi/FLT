/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianRefinement
public import FLT.Mazur.PolygonCompleteSmoothRotation

/-!
# Refinements of the actual complete-family smooth opens

The original refinement maps restrict to the actual relative smooth loci.
They preserve the identity marking, all other labels and the original cyclic
rotations. The restrictions retain identity and composition coherence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y T Z : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)
  (t : T ⟶ Spec (.of (PowerSeries K)))
  (p' : Z ⟶ exactVeroneseProj K n h) (q' : Z ⟶ T)
  (ht : IsPullback p' q' (exactVeroneseProjToBase K n h) t)
  (k : T ⟶ S) (hk : k ≫ s = t)
  [LocallyOfFinitePresentation q] [LocallyOfFinitePresentation q']

/-- Refinement pulls the actual relative smooth open back to the actual smooth open. -/
theorem completeCartesianRefinement_preimage_smoothLocus :
    completeCartesianRefinement K n h s p q hs t p' q' ht k hk ⁻¹ᵁ q.smoothLocus =
      q'.smoothLocus := by
  rw [← completeCartesian_preimage_smoothLocus K n h s p q hs,
    ← Scheme.Hom.comp_preimage, completeCartesianRefinement_fst,
    completeCartesian_preimage_smoothLocus K n h t p' q' ht]

/-- Restriction of the original refinement to the actual smooth opens. -/
def completeSmoothCartesianRefinement : (q'.smoothLocus : Scheme) ⟶ q.smoothLocus := by
  refine IsOpenImmersion.lift q.smoothLocus.ι
    (q'.smoothLocus.ι ≫ completeCartesianRefinement K n h s p q hs t p' q' ht k hk) ?_
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have he := congrArg (fun U : Z.Opens ↦ x.1 ∈ U)
    (completeCartesianRefinement_preimage_smoothLocus K n h s p q hs t p' q' ht k hk)
  exact he.mpr x.2

/-- The smooth refinement retains the original map of whole families. -/
@[reassoc] theorem completeSmoothCartesianRefinement_ι :
    completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk ≫ q.smoothLocus.ι =
      q'.smoothLocus.ι ≫ completeCartesianRefinement K n h s p q hs t p' q' ht k hk :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth refinement covers the given parameter map. -/
@[reassoc] theorem completeSmoothCartesianRefinement_toBase :
    completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk ≫
        q.smoothLocus.ι ≫ q = q'.smoothLocus.ι ≫ q' ≫ k := by
  rw [completeSmoothCartesianRefinement_ι_assoc, completeCartesianRefinement_snd]

/-- Every original smooth marking is unchanged by refinement of its parameters. -/
@[reassoc] theorem completeSmoothCartesianRefinement_marking (i : Fin n) :
    completeSmoothCartesianMarking K n h t p' q' ht i ≫
        completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk =
      k ≫ completeSmoothCartesianMarking K n h s p q hs i := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [Category.assoc, completeSmoothCartesianRefinement_ι,
    completeSmoothCartesianMarking_ι_assoc, completeCartesianRefinement_marking,
    Category.assoc, completeSmoothCartesianMarking_ι]

/-- Original rotations commute with the actual smooth refinement. -/
@[reassoc] theorem completeSmoothCartesianRefinement_rotation (a : ZMod n) :
    completeSmoothCartesianRotation K n h t p' q' ht a ≫
        completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk =
      completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk ≫
        completeSmoothCartesianRotation K n h s p q hs a := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [Category.assoc, completeSmoothCartesianRefinement_ι,
    completeSmoothCartesianRotation_ι_assoc, completeCartesianRefinement_rotation,
    Category.assoc, completeSmoothCartesianRotation_ι,
    completeSmoothCartesianRefinement_ι_assoc]

/-- Restricting the identity refinement gives the actual smooth identity. -/
@[simp] theorem completeSmoothCartesianRefinement_id :
    completeSmoothCartesianRefinement K n h s p q hs s p q hs (𝟙 S) (Category.id_comp s) =
      𝟙 _ := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [completeSmoothCartesianRefinement_ι, completeCartesianRefinement_id,
    Category.comp_id, Category.id_comp]

variable {U W : Scheme} (u : U ⟶ Spec (.of (PowerSeries K)))
  (p'' : W ⟶ exactVeroneseProj K n h) (q'' : W ⟶ U)
  (hu : IsPullback p'' q'' (exactVeroneseProjToBase K n h) u)
  (l : U ⟶ T) (hl : l ≫ t = u) [LocallyOfFinitePresentation q'']

/-- Smooth restrictions preserve composition of arbitrary original refinements. -/
theorem completeSmoothCartesianRefinement_comp :
    completeSmoothCartesianRefinement K n h t p' q' ht u p'' q'' hu l hl ≫
        completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk =
      completeSmoothCartesianRefinement K n h s p q hs u p'' q'' hu (l ≫ k)
        (by rw [Category.assoc, hk, hl]) := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [Category.assoc, completeSmoothCartesianRefinement_ι,
    completeSmoothCartesianRefinement_ι_assoc, completeCartesianRefinement_comp,
    completeSmoothCartesianRefinement_ι]

end FLT.Mazur.PolygonInfinitesimalStages
