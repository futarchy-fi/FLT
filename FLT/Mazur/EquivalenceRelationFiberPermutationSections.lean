/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteFiberComparison

/-!
# Original permutation sections of the entire relation fiber

The actual moving action graphs give disjoint open sections of the original
first-endpoint fiber. A complete frame makes these sections exhaustive, even
for field tests with an independent scalar extension.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)

/-- Each moving permutation gives its original section of the whole relation fiber. -/
def relationFiberSection (σ : Equiv.Perm I) :
    Spec (.of K) ⟶ pullback (relationFirst p q I o) u :=
  pullback.lift (u ≫ actionGraph e I o σ) (𝟙 _)
    (by rw [Category.assoc, actionGraph_first, Category.comp_id, Category.id_comp])

omit [Etale p] in
/-- The section retains the entire original relation arrow. -/
@[reassoc] theorem relationFiberSection_fst (σ : Equiv.Perm I) :
    relationFiberSection e I o u σ ≫ pullback.fst (relationFirst p q I o) u =
      u ≫ actionGraph e I o σ := pullback.lift_fst _ _ _

omit [Etale p] in
/-- The original coefficient point is unchanged. -/
@[reassoc] theorem relationFiberSection_snd (σ : Equiv.Perm I) :
    relationFiberSection e I o u σ ≫ pullback.snd (relationFirst p q I o) u = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The original permutation sections are open immersions of schemes. -/
instance relationFiberSection_isOpenImmersion (σ : Equiv.Perm I) :
    IsOpenImmersion (relationFiberSection e I o u σ) := by
  let _ := relationFirst_etale p q I o e
  exact UnramifiedSectionImmersion.isOpenImmersion
    (pullback.snd (relationFirst p q I o) u) _ (relationFiberSection_snd e I o u σ)

/-- Distinct permutations have disjoint images in the entire original relation fiber. -/
theorem relationFiberSection_disjoint (σ τ : Equiv.Perm I) (h : σ ≠ τ) :
    Disjoint (Set.range (relationFiberSection e I o u σ))
      (Set.range (relationFiberSection e I o u τ)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  have ha' := congrArg (pullback.fst (relationFirst p q I o) u) ha
  have hb' := congrArg (pullback.fst (relationFirst p q I o) u) hb
  rw [← Scheme.Hom.comp_apply, relationFiberSection_fst, Scheme.Hom.comp_apply] at ha' hb'
  exact Set.disjoint_left.mp (actionGraph_disjoint e I o σ τ h)
    ⟨u a, ha'⟩ ⟨u b, hb'⟩

/-- Every original relation test over a complete frame is one of the original sections. -/
theorem complete_relationFiber_factors_section (hu : Complete I o u)
    {L : Type} [Field L] (z : Spec (.of L) ⟶ pullback (relationFirst p q I o) u) :
    ∃ σ : Equiv.Perm I,
      (z ≫ pullback.snd (relationFirst p q I o) u) ≫ relationFiberSection e I o u σ = z := by
  let r := z ≫ pullback.fst (relationFirst p q I o) u
  have hc : Complete I o (r ≫ relationFirst p q I o) := by
    simpa only [r, Category.assoc] using complete_relationFiber_test I o u hu z
  obtain ⟨σ, hσ, _⟩ := complete_original_arrow_unique_permutation e I o
    (r ≫ relationFirst p q I o) (r ≫ relationSecond p q I o)
    (r ≫ relationArrow p q I o)
    (by simp only [Category.assoc, relationArrow_first])
    (by simp only [Category.assoc, relationArrow_second]) hc
  refine ⟨σ, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, relationFiberSection_fst, ← Category.assoc]
    have hz : (z ≫ pullback.snd (relationFirst p q I o) u) ≫ u =
        r ≫ relationFirst p q I o := by
      simp only [r, Category.assoc, pullback.condition]
    rw [hz]
    exact actionGraph_factor e I o r σ hσ
  · rw [Category.assoc, relationFiberSection_snd, Category.comp_id]

/-- Completeness makes the original permutation sections cover every fiber point. -/
theorem complete_relationFiber_sections_surjective (hu : Complete I o u) :
    Function.Surjective (fun σ ↦ relationFiberSection e I o u σ default) := by
  intro x
  let z := (pullback (relationFirst p q I o) u).fromSpecResidueField x
  obtain ⟨σ, hσ⟩ := complete_relationFiber_factors_section e I o u hu z
  refine ⟨σ, ?_⟩
  have h := congrArg (fun f ↦ f default) hσ
  rw [Scheme.Hom.comp_apply] at h
  have hx : z default = x := Scheme.fromSpecResidueField_apply x default
  exact (congrArg (relationFiberSection e I o u σ)
    (Subsingleton.elim default ((z ≫ pullback.snd _ _) default))).trans (h.trans hx)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
