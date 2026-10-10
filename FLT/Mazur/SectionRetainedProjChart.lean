/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjRegradedEvaluation
public import FLT.Mazur.SectionRetainedChartComparison
public import FLT.Mazur.SectionGradedProjChartPullback

/-!
# Local morphisms to the retained section-ring Proj

Restrict original line-coordinate evaluation to the retained section ring.
The resulting Proj charts are independent of line coordinates and natural
under further pullback because their fractions are the original section ratios.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedProjChart

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme} (p : Y ⟶ X) (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (e : (pullback p).obj L ≅ structureModule Y)
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- Original line-coordinate evaluation restricted to the actual retained ring. -/
def ringHom : RetainedSubringGrading.ring (grade L ⊤) q →+* Γ(Y, ⊤) :=
  (SectionGradedProjChart.ringHom p L e).comp
    (RetainedSubringGrading.ring (grade L ⊤) q).subtype

/-- Evaluating retained fractions is evaluating the corresponding original section fractions. -/
theorem evaluation_eq (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) :
    GradedProjUnitChart.evaluation (RetainedSubringGrading.grade (grade L ⊤) q)
      (ringHom p L e q) f hf =
    (SectionGradedProjChart.evaluation p L e (f : SectionGradedSum.Sections L ⊤) hf).comp
      (RetainedSubringLocalization.inclusion (grade L ⊤) q f) :=
  (GradedProjRegradedEvaluation.evaluation_comp
    (RetainedSubringGrading.grade (grade L ⊤) q) (grade L ⊤)
    (RetainedSubringGrading.ring (grade L ⊤) q).subtype (q * ·) (fun _ _ ha ↦ ha)
    (SectionGradedProjChart.ringHom p L e) f hf
    (RetainedSubringLocalization.powers_le (grade L ⊤) q f)).symm

/-- A unit retained homogeneous section gives the actual local map to the retained Proj. -/
def toProj (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) {d : ℕ}
    (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d) :
    Y ⟶ Proj (RetainedSubringGrading.grade (grade L ⊤) q) :=
  GradedProjUnitChart.toProj _ (ringHom p L e q) f hf hd hpos

/-- A change of line coordinates does not change the retained Proj morphism. -/
theorem toProj_independent (e' : (pullback p).obj L ≅ structureModule Y)
    (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) (hf' : IsUnit (ringHom p L e' q f))
    {d : ℕ} (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d) :
    toProj p L e q f hf hd hpos = toProj p L e' q f hf' hd hpos := by
  unfold toProj GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  rw [evaluation_eq, evaluation_eq,
    SectionGradedProjChart.evaluation_independent p L e e'
      (f : SectionGradedSum.Sections L ⊤) hf hf']

/-- Further pullback preserves the retained Proj map in arbitrary line coordinates. -/
@[reassoc]
theorem toProj_naturality (k : Z ⟶ Y)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) (hf' : IsUnit (ringHom (k ≫ p) L e' q f))
    {d : ℕ} (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d) :
    k ≫ toProj p L e q f hf hd hpos = toProj (k ≫ p) L e' q f hf' hd hpos := by
  unfold toProj GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  simp only [← Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 3
  apply CommRingCat.hom_ext
  change k.appTop.hom.comp (GradedProjUnitChart.evaluation _ (ringHom p L e q) f hf) =
    GradedProjUnitChart.evaluation _ (ringHom (k ≫ p) L e' q) f hf'
  rw [evaluation_eq, evaluation_eq, ← RingHom.comp_assoc,
    SectionGradedProjChart.evaluation_naturality p L e k e'
      (f : SectionGradedSum.Sections L ⊤) hf hf']

/-- Two unit retained homogeneous denominators define the same local Proj morphism. -/
theorem toProj_eq (f g : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) (hg : IsUnit (ringHom p L e q g))
    {d n : ℕ} (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d)
    (hn : g ∈ RetainedSubringGrading.grade (grade L ⊤) q n) (hnpos : 0 < n) :
    toProj p L e q f hf hd hpos = toProj p L e q g hg hn hnpos :=
  GradedProjUnitChart.toProj_eq _ (ringHom p L e q) hd hpos hn hnpos hf hg

/-- Equal structure morphisms give equal retained charts, in arbitrary line coordinates. -/
theorem toProj_congr {p' : Y ⟶ X} (hp : p = p')
    (e' : (pullback p').obj L ≅ structureModule Y)
    (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (ringHom p L e q f)) (hf' : IsUnit (ringHom p' L e' q f))
    {d : ℕ} (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d) :
    toProj p L e q f hf hd hpos = toProj p' L e' q f hf' hd hpos := by
  subst p'
  exact toProj_independent p L e q e' f hf hf' hd hpos

/-- Original homogeneous generators retain unit coordinates after further pullback. -/
@[reassoc]
theorem toProj_pullback (k : Z ⟶ Y) {d : ℕ} (s : Γ(tensorPower L (q * d), ⊤))
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ (q * d) s)))
    (hd : 0 < d) :
    k ≫ toProj p L e q (SectionRetainedChartComparison.insertion L q d s) hs
      (SectionRetainedChartComparison.insertion_mem L q d s) hd =
    toProj (k ≫ p) L (SectionGradedProjChart.pullTrivialization p L e k) q
      (SectionRetainedChartComparison.insertion L q d s)
      (SectionGradedProjChart.ringHom_isUnit_pullback p L e k _ s hs)
      (SectionRetainedChartComparison.insertion_mem L q d s) hd :=
  toProj_naturality p L e q k _ _ _ _ _ _

end FLT.Mazur.SectionRetainedProjChart
