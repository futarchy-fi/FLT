/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedActionGraphs

/-!
# The normalized permutation relation embeds openly in the full original relation

The finite disjoint union of actual action graphs maps by an open immersion into
the full original relation. It contains every geometric related pair of complete
frames. Its open image is an honest scheme restriction, retaining nilpotents;
it is not asserted to contain all pairs of incomplete frames.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- Distinct normalized permutation graphs have disjoint images in the full relation. -/
theorem actionGraph_disjoint (σ τ : Equiv.Perm I) (h : σ ≠ τ) :
    Disjoint (Set.range (actionGraph e I o σ)) (Set.range (actionGraph e I o τ)) := by
  let _ := actionGraph_isOpenImmersion e I o σ
  let _ := actionGraph_isOpenImmersion e I o τ
  apply Set.disjoint_left.mpr
  intro x hx hy
  let z := (fullRelation p q I o).fromSpecResidueField x
  have hσ : Set.range z ⊆ Set.range (actionGraph e I o σ) := by
    rintro _ ⟨t, rfl⟩
    simpa only [z, Scheme.fromSpecResidueField_apply] using hx
  have hτ : Set.range z ⊆ Set.range (actionGraph e I o τ) := by
    rintro _ ⟨t, rfl⟩
    simpa only [z, Scheme.fromSpecResidueField_apply] using hy
  apply h
  apply actionGraph_unique e I o z σ τ
  · exact ⟨IsOpenImmersion.lift _ z hσ, IsOpenImmersion.lift_fac _ z hσ⟩
  · exact ⟨IsOpenImmersion.lift _ z hτ, IsOpenImmersion.lift_fac _ z hτ⟩

/-- The actual action relation scheme, a finite disjoint union of normalized frame sources. -/
def permutationRelation : Scheme := ∐ fun _ : Equiv.Perm I ↦ source p q I o

/-- The comparison with the full original relation keeps both independent endpoints. -/
def relationComparison : permutationRelation (p := p) (q := q) I o ⟶ fullRelation p q I o :=
  Sigma.desc (actionGraph e I o)

omit [Etale p] in
/-- On each permutation component the comparison is the original action graph. -/
@[reassoc] theorem component_relationComparison (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫ relationComparison e I o =
      actionGraph e I o σ := Sigma.ι_comp_desc _ _

omit [Etale p] in
/-- The first endpoint is unchanged on each actual permutation component. -/
@[reassoc] theorem component_relationComparison_first (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      relationComparison e I o ≫ relationFirst p q I o = 𝟙 _ := by
  rw [← Category.assoc, component_relationComparison, actionGraph_first]

omit [Etale p] in
/-- The second endpoint is the endpoint-moving action on each component. -/
@[reassoc] theorem component_relationComparison_second (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      relationComparison e I o ≫ relationSecond p q I o = (action e I o σ).hom := by
  rw [← Category.assoc, component_relationComparison, actionGraph_second]

omit [Etale p] in
/-- Every component keeps the original full relation arrow. -/
@[reassoc] theorem component_relationComparison_arrow (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      relationComparison e I o ≫ relationArrow p q I o = actionArrow I o σ := by
  rw [← Category.assoc, component_relationComparison, actionGraph_arrow]

/-- The actual permutation relation is an open subscheme of the full original relation. -/
theorem relationComparison_isOpenImmersion : IsOpenImmersion (relationComparison e I o) := by
  let _ := fun σ ↦ actionGraph_isOpenImmersion e I o σ
  exact AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (actionGraph e I o)
    (fun σ τ h ↦ actionGraph_disjoint e I o σ τ h)

/-- The exact open scheme locus where the action relation agrees with the full relation. -/
def actionRelationOpen : (fullRelation p q I o).Opens := by
  let _ := relationComparison_isOpenImmersion e I o
  exact (relationComparison e I o).opensRange

/-- Scheme-level identification with the full original relation restricted to its open image. -/
def actionRelationIso : permutationRelation (p := p) (q := q) I o ≅
    (actionRelationOpen e I o).toScheme := by
  let _ := relationComparison_isOpenImmersion e I o
  exact IsOpenImmersion.isoOfRangeEq (relationComparison e I o)
    (actionRelationOpen e I o).ι (by simp [actionRelationOpen])

/-- The identification retains the full original relation map as a scheme morphism. -/
@[reassoc] theorem actionRelationIso_inclusion :
    (actionRelationIso e I o).hom ≫ (actionRelationOpen e I o).ι =
      relationComparison e I o := by
  let _ := relationComparison_isOpenImmersion e I o
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (by simp [actionRelationOpen])

variable {K : Type} [Field K] (z : Spec (.of K) ⟶ fullRelation p q I o)
  (h₁ : Complete I o (z ≫ relationFirst p q I o))
  (h₂ : Complete I o (z ≫ relationSecond p q I o))

include h₁ h₂ in
/-- Every original related pair of complete geometric frames lies in the open comparison. -/
theorem complete_factors_relationComparison :
    ∃ w : Spec (.of K) ⟶ permutationRelation (p := p) (q := q) I o,
      w ≫ relationComparison e I o = z := by
  have ha := congrArg (fun f ↦ z ≫ f) (relationArrow_first p q I o)
  have hb := congrArg (fun f ↦ z ≫ f) (relationArrow_second p q I o)
  obtain ⟨σ, hσ, _⟩ := (original_arrow_iff_unique_permutation e I o
    (z ≫ relationFirst p q I o) (z ≫ relationSecond p q I o) h₁ h₂).mp
      ⟨z ≫ relationArrow p q I o, by simpa only [Category.assoc] using ha,
        by simpa only [Category.assoc] using hb⟩
  refine ⟨(z ≫ relationFirst p q I o) ≫
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ, ?_⟩
  rw [Category.assoc, component_relationComparison]
  exact actionGraph_factor e I o z σ hσ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
