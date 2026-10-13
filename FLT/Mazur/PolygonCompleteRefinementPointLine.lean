/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRefinementSquares
public import FLT.Mazur.PolygonCompleteCartesianPointLine
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Original point lines along complete-family refinements

The entire labeled Cartier ideal, its positive line and its canonical section
survive arbitrary refinement. Composite refinement gives the actual sheaf
pullback triangle, including the label-zero origin line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
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

/-- Refinement retains the whole original labeled point ideal. -/
theorem completeCartesianRefinement_pointIdeal (i : Fin n) :
    (completeCartesianMarking K n h s p q hs i).ker.comap
        (completeCartesianRefinement K n h s p q hs t p' q' ht k hk) =
      (completeCartesianMarking K n h t p' q' ht i).ker := by
  rw [← completeCartesianMarking_ker, ← Scheme.IdealSheafData.comap_comp,
    completeCartesianRefinement_fst, completeCartesianMarking_ker]

/-- The original ideal-module pullback comparison is invertible under refinement. -/
theorem completeCartesianRefinement_pointIdeal_isIso (i : Fin n) :
    IsIso (idealModulePullbackHom (completeCartesianMarking K n h s p q hs i).ker
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk)) :=
  relativeCartierIdealPullback_originalSquare
    (completeCartesianRefinement_isPullback K n h s p q hs t p' q' ht k hk) _
    (completeCartesianMarking_relativeCartier K n h s p q hs i)

/-- The actual positive point line comparison along the original refinement map. -/
def completeCartesianRefinementPointLineIso (i : Fin n) :
    (Scheme.Modules.pullback
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk)).obj
        (completeCartesianPointLine K n h s p q hs i) ≅
      completeCartesianPointLine K n h t p' q' ht i := by
  let _ := completeCartesianRefinement_pointIdeal_isIso K n h s p q hs t p' q' ht k hk i
  exact divisorLinePullbackIsoOfEq _
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianMarking_relativeCartier K n h t p' q' ht i).1
    (completeCartesianRefinement_pointIdeal K n h s p q hs t p' q' ht k hk i)

/-- Point-line refinement preserves its canonical vanishing section, with multiplicity. -/
theorem completeCartesianRefinementPointLineIso_section (i : Fin n) :
    DivisorLineSectionCompatible
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk)
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1
      (completeCartesianMarking_relativeCartier K n h t p' q' ht i).1
      (completeCartesianRefinementPointLineIso K n h s p q hs t p' q' ht k hk i) := by
  let _ := completeCartesianRefinement_pointIdeal_isIso K n h s p q hs t p' q' ht k hk i
  exact divisorLinePullbackIsoOfEq_section _ _ _ _

variable {U W : Scheme} (u : U ⟶ Spec (.of (PowerSeries K)))
  (p'' : W ⟶ exactVeroneseProj K n h) (q'' : W ⟶ U)
  (hu : IsPullback p'' q'' (exactVeroneseProjToBase K n h) u)
  (l : U ⟶ T) (hl : l ≫ t = u)

/-- The original point lines satisfy the actual composite-refinement triangle. -/
theorem completeCartesianRefinementPointLineIso_comp (i : Fin n) :
    LinePullbackTriangle
      (completeCartesianRefinement K n h t p' q' ht u p'' q'' hu l hl)
      (completeCartesianRefinement K n h s p q hs t p' q' ht k hk)
      (completeCartesianRefinement K n h s p q hs u p'' q'' hu (l ≫ k)
        (by rw [Category.assoc, hk, hl]))
      (completeCartesianRefinement_comp K n h s p q hs t p' q' ht k hk u p'' q'' hu l hl)
      (completeCartesianRefinementPointLineIso K n h s p q hs t p' q' ht k hk i)
      (completeCartesianRefinementPointLineIso K n h t p' q' ht u p'' q'' hu l hl i)
      (completeCartesianRefinementPointLineIso K n h s p q hs u p'' q'' hu (l ≫ k)
        (by rw [Category.assoc, hk, hl]) i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeCartesianRefinementPointLineIso_section K n h s p q hs t p' q' ht k hk i)
    (completeCartesianRefinementPointLineIso_section K n h t p' q' ht u p'' q'' hu l hl i)
    (completeCartesianRefinementPointLineIso_section K n h s p q hs u p'' q'' hu (l ≫ k)
      (by rw [Category.assoc, hk, hl]) i)

end FLT.Mazur.PolygonInfinitesimalStages
