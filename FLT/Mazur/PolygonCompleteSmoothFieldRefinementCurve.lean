/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldGroupHom
public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Full smooth field comparisons between independently chosen original squares

The original refinement is an isomorphism of full DR curves. Its identity and
composition laws retain the actual original projections and marked sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (p' : Z ⟶ exactVeroneseProj K n h) (q' : Z ⟶ Spec (.of L))
  (ht : IsPullback p' q' (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)

local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs
local notation "D" => completeFieldGeneralizedCurve K n h L a ha p' q' ht
local notation "f" => completeFieldRefinement K n h L a p q hs p' q' ht

/-- The original same-field refinement is an isomorphism of relative curves. -/
def completeFieldRefinementOverIso : Over.mk q' ≅ Over.mk q where
  hom := f
  inv := completeFieldRefinement K n h L a p' q' ht p q hs
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply ht.hom_ext
    · simp only [Over.comp_left, completeFieldRefinement, Over.homMk_left,
        Category.assoc, completeCartesianRefinement_fst, Over.id_left, Category.id_comp]
    · exact ((f ≫ completeFieldRefinement K n h L a p' q' ht p q hs).w).trans
        (Category.id_comp _).symm
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply hs.hom_ext
    · simp only [Over.comp_left, completeFieldRefinement, Over.homMk_left,
        Category.assoc, completeCartesianRefinement_fst, Over.id_left, Category.id_comp]
    · exact ((completeFieldRefinement K n h L a p' q' ht p q hs ≫ f).w).trans
        (Category.id_comp _).symm

/-- The original refinement preserves the whole constructed DR object. -/
def completeFieldRefinementCurveIso (i : Fin n) : D i ≅ E i := by
  let e := completeFieldRefinementOverIso K n h L a p q hs p' q' ht
  let _ := completeFieldCommGrp K n h L a ha p' q' ht i
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  let _ : IsMonHom e.hom := completeFieldRefinement_isMonHom K n h L a ha p q hs p' q' ht i
  exact GeneralizedEllipticCurve.isoMk e e
    (by rw [completeFieldGeneralizedCurve_inclusion, completeFieldGeneralizedCurve_inclusion,
      Category.id_comp, Category.comp_id])
    (IsMonHom.mul_hom e.hom)

/-- The DR comparison retains exactly the map to the original complete total space. -/
@[reassoc] theorem completeFieldRefinementCurveIso_fst (i : Fin n) :
    (completeFieldRefinementCurveIso K n h L a ha p q hs p' q' ht i).hom.curve.left ≫ p = p' :=
  completeCartesianRefinement_fst K n h s p q hs s p' q' ht (𝟙 _) (by simp)

/-- The actual original refinement preserves every original marked section. -/
theorem completeFieldRefinementCurveIso_marking (i j : Fin n) :
    completeFieldMarkedPoint K n h L a p' q' ht j ≫
        (completeFieldRefinementCurveIso K n h L a ha p q hs p' q' ht i).hom.curve =
      completeFieldMarkedPoint K n h L a p q hs j := by
  apply Over.OverMorphism.ext
  exact (completeCartesianRefinement_marking K n h s p q hs s p' q' ht
    (𝟙 _) (by simp) j).trans (Category.id_comp _)

/-- Refinement by the identity is the identity of the full original DR object. -/
theorem completeFieldRefinementCurveIso_refl (i : Fin n) :
    completeFieldRefinementCurveIso K n h L a ha p q hs p q hs i = Iso.refl (E i) := by
  apply Iso.ext
  apply GeneralizedEllipticCurve.forgetCurve.map_injective
  apply Over.OverMorphism.ext
  exact completeCartesianRefinement_id K n h s p q hs

variable {W : Scheme} (p'' : W ⟶ exactVeroneseProj K n h) (q'' : W ⟶ Spec (.of L))
  (hu : IsPullback p'' q'' (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The two refinement paths agree as full DR isomorphisms, including their group laws. -/
theorem completeFieldRefinementCurveIso_trans (i : Fin n) :
    completeFieldRefinementCurveIso K n h L a ha p' q' ht p'' q'' hu i ≪≫
        completeFieldRefinementCurveIso K n h L a ha p q hs p' q' ht i =
      completeFieldRefinementCurveIso K n h L a ha p q hs p'' q'' hu i := by
  apply Iso.ext
  apply GeneralizedEllipticCurve.forgetCurve.map_injective
  apply Over.OverMorphism.ext
  apply hs.hom_ext
  · change ((completeFieldRefinementCurveIso K n h L a ha p' q' ht p'' q'' hu i).hom.curve.left ≫
      (completeFieldRefinementCurveIso K n h L a ha p q hs p' q' ht i).hom.curve.left) ≫ p =
        (completeFieldRefinementCurveIso K n h L a ha p q hs p'' q'' hu i).hom.curve.left ≫ p
    rw [Category.assoc,
      completeFieldRefinementCurveIso_fst K n h L a ha p q hs p' q' ht i,
      completeFieldRefinementCurveIso_fst K n h L a ha p' q' ht p'' q'' hu i,
      completeFieldRefinementCurveIso_fst K n h L a ha p q hs p'' q'' hu i]
  · exact (((completeFieldRefinementCurveIso K n h L a ha p' q' ht p'' q'' hu i).hom.curve ≫
      (completeFieldRefinementCurveIso K n h L a ha p q hs p' q' ht i).hom.curve).w).trans
        (completeFieldRefinementCurveIso K n h L a ha p q hs p'' q'' hu i).hom.curve.w.symm

end FLT.Mazur.PolygonInfinitesimalStages
