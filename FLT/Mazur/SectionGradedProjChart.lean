/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjUnitChart
public import FLT.Mazur.SectionGradedCoordinateIndependence
public import FLT.Mazur.SectionGradedPullbackRing

/-!
# Actual local maps to the Proj of the section ring

On a scheme mapping to the original scheme, a trivialization of the pulled
line bundle evaluates all global tensor-power sections. A positive-degree
section with unit coordinate gives a scheme map into the original Proj.
The resulting map is independent of both the trivialization and the choice
of an invertible positive-degree section on this fixed domain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjChart
open FCurve SectionGradedSum SectionGradedCoordinateEvaluation SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules)
  (e : (pullback p).obj L ≅ structureModule Y)

/-- Evaluate original global sections using actual tensor-power pullback and line coordinates. -/
def ringHom : SectionGradedSum.Sections L ⊤ →+* Γ(Y, ⊤) :=
  (ringEval e ⊤).comp (SectionGradedPullback.ringHom p L)

/-- Evaluation on a pulled-back homogeneous section retains its degree. -/
lemma ringHom_of (n : ℕ) (s : SectionGradedMultiplication.Piece L ⊤ n) :
    ringHom p L e (of L ⊤ n s) =
      coordinate e n ⊤ (SectionGradedPullback.pull p L n ⊤ s) := by
  change ringEval e ⊤ (SectionGradedPullback.sumMap p L (of L ⊤ n s)) = _
  rw [SectionGradedPullback.sumMap_of, ringEval_of]

variable [Fact (LocallyFreeRankOne L)]

/-- The affine Proj-chart evaluation on this actual trivializing domain. -/
def evaluation (f : SectionGradedSum.Sections L ⊤) (hf : IsUnit (ringHom p L e f)) :
    HomogeneousLocalization.Away (grade L ⊤) f →+* Γ(Y, ⊤) :=
  GradedProjUnitChart.evaluation (grade L ⊤) (ringHom p L e) f hf

/-- A local map from the trivializing domain into the Proj of the original full section ring. -/
def toProj (f : SectionGradedSum.Sections L ⊤) (hf : IsUnit (ringHom p L e f))
    {d : ℕ} (hd : f ∈ grade L ⊤ d) (hpos : 0 < d) : Y ⟶ Proj (grade L ⊤) :=
  GradedProjUnitChart.toProj (grade L ⊤) (ringHom p L e) f hf hd hpos

/-- The chart evaluation is independent of line coordinates on the pulled-back bundle. -/
lemma evaluation_independent (e' : (pullback p).obj L ≅ structureModule Y)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hf' : IsUnit (ringHom p L e' f)) :
    evaluation p L e f hf = evaluation p L e' f hf' := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := SectionGradedPullback.ringHom_mem_grade p L c.den.property
  obtain ⟨t, ht⟩ := SectionGradedPullback.ringHom_mem_grade p L c.num.property
  have he : evaluation p L e f hf (HomogeneousLocalization.mk c) • s = t := by
    apply (coordinate_equation_iff e ⊤ c.deg _ s t).mp
    rw [← ringEval_of, ← ringEval_of, hs, ht]
    exact GradedProjUnitChart.evaluation_mk_mul (grade L ⊤) (ringHom p L e) f hf c
  apply (GradedProjUnitChart.denominator_isUnit
    (grade L ⊤) (ringHom p L e') f hf' c).mul_left_inj.mp
  unfold evaluation
  rw [GradedProjUnitChart.evaluation_mk_mul]
  change _ * ringEval e' ⊤ (SectionGradedPullback.ringHom p L c.den) =
    ringEval e' ⊤ (SectionGradedPullback.ringHom p L c.num)
  rw [← hs, ← ht, ringEval_of, ringEval_of]
  exact (coordinate_equation_iff e' ⊤ c.deg _ s t).mpr he

/-- The actual map into Proj is independent of the chosen pulled-back trivialization. -/
lemma toProj_independent (e' : (pullback p).obj L ≅ structureModule Y)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hf' : IsUnit (ringHom p L e' f))
    {d : ℕ} (hd : f ∈ grade L ⊤ d) (hpos : 0 < d) :
    toProj p L e f hf hd hpos = toProj p L e' f hf' hd hpos := by
  unfold toProj GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  rw [show GradedProjUnitChart.evaluation (grade L ⊤) (ringHom p L e) f hf =
    GradedProjUnitChart.evaluation (grade L ⊤) (ringHom p L e') f hf' from
      evaluation_independent p L e e' f hf hf']

/-- Any two invertible positive-degree sections give the same local map into Proj. -/
lemma toProj_eq (f g : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hg : IsUnit (ringHom p L e g))
    {d n : ℕ} (hd : f ∈ grade L ⊤ d) (hpos : 0 < d)
    (hn : g ∈ grade L ⊤ n) (hnpos : 0 < n) :
    toProj p L e f hf hd hpos = toProj p L e g hg hn hnpos :=
  GradedProjUnitChart.toProj_eq (grade L ⊤) (ringHom p L e) hd hpos hn hnpos hf hg

end FLT.Mazur.SectionGradedProjChart
