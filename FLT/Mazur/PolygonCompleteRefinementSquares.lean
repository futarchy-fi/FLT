/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothRefinement

/-!
# Cartesian coherence of complete-family refinements

The refinement morphisms and their smooth restrictions are actual base-change
squares. In particular the smooth inclusion square is cartesian; this records
scheme structure, not only compatibility of smooth geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y T Z : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)
  (t : T ⟶ Spec (.of (PowerSeries K)))
  (p' : Z ⟶ exactVeroneseProj K n h) (q' : Z ⟶ T)
  (ht : IsPullback p' q' (exactVeroneseProjToBase K n h) t)
  (k : T ⟶ S) (hk : k ≫ s = t)

/-- The actual refinement is a cartesian square over the parameter map. -/
theorem completeCartesianRefinement_isPullback :
    IsPullback (completeCartesianRefinement K n h s p q hs t p' q' ht k hk) q' q k := by
  have he : IsPullback
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk ≫ p) q'
      (exactVeroneseProjToBase K n h) (k ≫ s) := by
    rw [completeCartesianRefinement_fst, hk]
    exact ht
  exact he.of_right (completeCartesianRefinement_snd K n h s p q hs t p' q' ht k hk) hs

variable [LocallyOfFinitePresentation q] [LocallyOfFinitePresentation q']

/-- The two original smooth inclusions form a cartesian refinement square. -/
theorem completeSmoothCartesianRefinement_inclusion_isPullback :
    IsPullback (completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk)
      q'.smoothLocus.ι q.smoothLocus.ι
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk) := by
  apply IsOpenImmersion.isPullback
  · exact (completeSmoothCartesianRefinement_ι K n h s p q hs t p' q' ht k hk).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      completeCartesianRefinement_preimage_smoothLocus K n h s p q hs t p' q' ht k hk

/-- The actual relative smooth loci themselves form a cartesian square over the base. -/
theorem completeSmoothCartesianRefinement_isPullback :
    IsPullback (completeSmoothCartesianRefinement K n h s p q hs t p' q' ht k hk)
      (q'.smoothLocus.ι ≫ q') (q.smoothLocus.ι ≫ q) k :=
  (completeSmoothCartesianRefinement_inclusion_isPullback K n h s p q hs
    t p' q' ht k hk).paste_vert
      (completeCartesianRefinement_isPullback K n h s p q hs t p' q' ht k hk)

end FLT.Mazur.PolygonInfinitesimalStages
