/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFiberMarkings

/-!
# Original markings on specified cartesian squares

The markings lift uniquely to any chosen base-change square. Comparison of
squares retains every label and its original section; their ranges stay disjoint.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original labeled marking on the specified cartesian square. -/
def completeCartesianMarking (i : Fin n) : S ⟶ Y :=
  hs.lift (s ≫ completeBaseMarking K n h i) (𝟙 S)
    (by rw [Category.assoc, completeBaseMarking_toBase]; simp)

/-- The lifted marking retains its labeled section in the original total space. -/
@[reassoc (attr := simp)] theorem completeCartesianMarking_fst (i : Fin n) :
    completeCartesianMarking K n h s p q hs i ≫ p = s ≫ completeBaseMarking K n h i :=
  hs.lift_fst _ _ _

/-- The lifted marking is a section of the specified structure map. -/
@[reassoc (attr := simp)] theorem completeCartesianMarking_snd (i : Fin n) :
    completeCartesianMarking K n h s p q hs i ≫ q = 𝟙 S :=
  hs.lift_snd _ _ _

/-- Its original labeled section and its base map uniquely determine the lifted marking. -/
theorem completeCartesianMarking_unique (i : Fin n) (t : S ⟶ Y)
    (htp : t ≫ p = s ≫ completeBaseMarking K n h i) (htq : t ≫ q = 𝟙 S) :
    t = completeCartesianMarking K n h s p q hs i := by
  apply hs.hom_ext
  · exact htp.trans (completeCartesianMarking_fst K n h s p q hs i).symm
  · exact htq.trans (completeCartesianMarking_snd K n h s p q hs i).symm

/-- Comparison with the chosen pullback preserves the original labeling. -/
@[reassoc] theorem completeCartesianMarking_comparison (i : Fin n) :
    completeCartesianMarking K n h s p q hs i ≫ hs.isoPullback.hom =
      completeFiberMarking K n h s i := by
  apply pullback.hom_ext
  · rw [Category.assoc, hs.isoPullback_hom_fst, completeCartesianMarking_fst,
      completeFiberMarking_fst]
  · rw [Category.assoc, hs.isoPullback_hom_snd, completeCartesianMarking_snd,
      completeFiberMarking_snd]

/-- Every chosen square retains the pairwise disjoint original labels. -/
theorem completeCartesianMarkings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (completeCartesianMarking K n h s p q hs i))
      (Set.range (completeCartesianMarking K n h s p q hs j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have hp := congrArg p he
  simp only [← Scheme.Hom.comp_apply, completeCartesianMarking_fst] at hp
  exact Set.disjoint_left.mp (completeBaseMarkings_pairwise K n h hij)
    ⟨s x, rfl⟩ ⟨s y, hp⟩

end FLT.Mazur.PolygonInfinitesimalStages
