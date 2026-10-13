/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianRotation

/-!
# Refinement of the original complete-family squares

Every map of parameter schemes induces a unique map of the specified
cartesian squares. It preserves the original rotations and labeled markings;
identity and composite refinements agree as actual scheme morphisms.
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

/-- The unique refinement retaining both projections of the original chosen square. -/
def completeCartesianRefinement : Z ⟶ Y :=
  hs.lift p' (q' ≫ k) (by rw [Category.assoc, hk]; exact ht.w)

/-- Refinement preserves the original map into the complete total space. -/
@[reassoc] theorem completeCartesianRefinement_fst :
    completeCartesianRefinement K n h s p q hs t p' q' ht k hk ≫ p = p' :=
  hs.lift_fst _ _ _

/-- Refinement covers exactly the chosen parameter map. -/
@[reassoc] theorem completeCartesianRefinement_snd :
    completeCartesianRefinement K n h s p q hs t p' q' ht k hk ≫ q = q' ≫ k :=
  hs.lift_snd _ _ _

/-- The projections uniquely determine the entire refinement map. -/
theorem completeCartesianRefinement_unique (r : Z ⟶ Y)
    (hrp : r ≫ p = p') (hrq : r ≫ q = q' ≫ k) :
    r = completeCartesianRefinement K n h s p q hs t p' q' ht k hk := by
  apply hs.hom_ext
  · exact hrp.trans (completeCartesianRefinement_fst K n h s p q hs t p' q' ht k hk).symm
  · exact hrq.trans (completeCartesianRefinement_snd K n h s p q hs t p' q' ht k hk).symm

/-- Refinement retains every original marking, with its original label. -/
@[reassoc] theorem completeCartesianRefinement_marking (i : Fin n) :
    completeCartesianMarking K n h t p' q' ht i ≫
        completeCartesianRefinement K n h s p q hs t p' q' ht k hk =
      k ≫ completeCartesianMarking K n h s p q hs i := by
  apply hs.hom_ext
  · rw [Category.assoc, completeCartesianRefinement_fst, completeCartesianMarking_fst,
      Category.assoc, completeCartesianMarking_fst, ← hk, Category.assoc]
  · rw [Category.assoc, completeCartesianRefinement_snd,
      completeCartesianMarking_snd_assoc,
      Category.assoc, completeCartesianMarking_snd, Category.comp_id]

/-- Refinement intertwines the original whole-family rotations. -/
@[reassoc] theorem completeCartesianRefinement_rotation (a : ZMod n) :
    completeCartesianRotation K n h t p' q' ht a ≫
        completeCartesianRefinement K n h s p q hs t p' q' ht k hk =
      completeCartesianRefinement K n h s p q hs t p' q' ht k hk ≫
        completeCartesianRotation K n h s p q hs a := by
  apply hs.hom_ext
  · rw [Category.assoc, completeCartesianRefinement_fst, completeCartesianRotation_fst,
      Category.assoc, completeCartesianRotation_fst, completeCartesianRefinement_fst_assoc]
  · rw [Category.assoc, completeCartesianRefinement_snd,
      completeCartesianRotation_snd_assoc, Category.assoc, completeCartesianRotation_snd,
      completeCartesianRefinement_snd]

/-- The identity refinement is the identity of the actual chosen square. -/
@[simp] theorem completeCartesianRefinement_id :
    completeCartesianRefinement K n h s p q hs s p q hs (𝟙 S) (Category.id_comp s) =
      𝟙 Y := by
  apply hs.hom_ext
  · rw [completeCartesianRefinement_fst, Category.id_comp]
  · rw [completeCartesianRefinement_snd, Category.comp_id, Category.id_comp]

variable {U W : Scheme} (u : U ⟶ Spec (.of (PowerSeries K)))
  (p'' : W ⟶ exactVeroneseProj K n h) (q'' : W ⟶ U)
  (hu : IsPullback p'' q'' (exactVeroneseProjToBase K n h) u)
  (l : U ⟶ T) (hl : l ≫ t = u)

/-- Iterated refinement agrees with refinement by the composite parameter map. -/
theorem completeCartesianRefinement_comp :
    completeCartesianRefinement K n h t p' q' ht u p'' q'' hu l hl ≫
        completeCartesianRefinement K n h s p q hs t p' q' ht k hk =
      completeCartesianRefinement K n h s p q hs u p'' q'' hu (l ≫ k)
        (by rw [Category.assoc, hk, hl]) := by
  apply hs.hom_ext
  · rw [Category.assoc, completeCartesianRefinement_fst,
      completeCartesianRefinement_fst, completeCartesianRefinement_fst]
  · rw [Category.assoc, completeCartesianRefinement_snd,
      completeCartesianRefinement_snd_assoc, completeCartesianRefinement_snd]

end FLT.Mazur.PolygonInfinitesimalStages
