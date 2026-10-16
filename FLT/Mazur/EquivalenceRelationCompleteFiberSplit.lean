/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiberPermutationSections

/-!
# Complete normalized frames split the full original relation fiber

The finite coproduct indexed by all permutations is isomorphic to the whole
original first-endpoint fiber. Component formulas preserve both independent
endpoints and the original relation and coefficient morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)

/-- The finite coproduct of the actual original permutation sections. -/
def relationFiberSplitMap : (∐ fun _ : Equiv.Perm I ↦ Spec (.of K)) ⟶
    pullback (relationFirst p q I o) u := Sigma.desc (relationFiberSection e I o u)

omit [Etale p] in
/-- Each component is exactly the original permutation section. -/
@[reassoc] theorem relationFiberSplitMap_component (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ ≫ relationFiberSplitMap e I o u =
      relationFiberSection e I o u σ := Sigma.ι_comp_desc _ _

/-- The disjoint original sections form an open immersion into the whole fiber. -/
instance relationFiberSplitMap_isOpenImmersion : IsOpenImmersion (relationFiberSplitMap e I o u) :=
  AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (relationFiberSection e I o u)
    (relationFiberSection_disjoint e I o u)

/-- Completeness identifies the whole original relation fiber as a finite split scheme. -/
theorem relationFiberSplitMap_isIso (hu : Complete I o u) :
    IsIso (relationFiberSplitMap e I o u) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro x
  obtain ⟨σ, hσ⟩ := complete_relationFiber_sections_surjective e I o u hu x
  refine ⟨(Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ) default, ?_⟩
  have h := congrArg (fun f ↦ f default) (relationFiberSplitMap_component e I o u σ)
  exact h.trans hσ

/-- The entire original relation fiber is a coproduct of copies of the original field. -/
def relationFiberSplitIso (hu : Complete I o u) :
    (∐ fun _ : Equiv.Perm I ↦ Spec (.of K)) ≅ pullback (relationFirst p q I o) u := by
  let _ := relationFiberSplitMap_isIso e I o u hu
  exact asIso (relationFiberSplitMap e I o u)

/-- The splitting keeps the entire original relation on every permutation component. -/
@[reassoc] theorem relationFiberSplitIso_original (hu : Complete I o u) (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ ≫
      (relationFiberSplitIso e I o u hu).hom ≫ pullback.fst (relationFirst p q I o) u =
        u ≫ actionGraph e I o σ := by
  change _ ≫ relationFiberSplitMap e I o u ≫ _ = _
  rw [← Category.assoc, relationFiberSplitMap_component, relationFiberSection_fst]

/-- The splitting retains the independently moving second endpoint. -/
@[reassoc] theorem relationFiberSplitIso_second (hu : Complete I o u) (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ ≫
      (relationFiberSplitIso e I o u hu).hom ≫ pullback.fst (relationFirst p q I o) u ≫
        relationSecond p q I o = u ≫ (action e I o σ).hom := by
  simpa only [Category.assoc, actionGraph_second] using
    congrArg (fun a ↦ a ≫ relationSecond p q I o)
      (relationFiberSplitIso_original e I o u hu σ)

/-- Every original coefficient morphism is retained by the fiber splitting. -/
@[reassoc] theorem relationFiberSplitIso_arrow (hu : Complete I o u) (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ ≫
      (relationFiberSplitIso e I o u hu).hom ≫ pullback.fst (relationFirst p q I o) u ≫
        relationArrow p q I o = u ≫ actionArrow I o σ := by
  simpa only [Category.assoc, actionGraph_arrow] using
    congrArg (fun a ↦ a ≫ relationArrow p q I o)
      (relationFiberSplitIso_original e I o u hu σ)

/-- All components retain the original base field coefficient map. -/
@[reassoc] theorem relationFiberSplitIso_scalar (hu : Complete I o u) (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ Spec (.of K)) σ ≫
      (relationFiberSplitIso e I o u hu).hom ≫ pullback.snd (relationFirst p q I o) u = 𝟙 _ := by
  change _ ≫ relationFiberSplitMap e I o u ≫ _ = _
  rw [← Category.assoc, relationFiberSplitMap_component, relationFiberSection_snd]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
