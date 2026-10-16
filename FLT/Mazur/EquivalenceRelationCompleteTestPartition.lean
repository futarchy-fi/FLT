/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSourceComparison

/-!
# Finite scheme decomposition of complete original relation tests

The inverse images of the actual permutation graphs partition an arbitrary
complete-support test. Their finite coproduct is isomorphic to the entire test,
including nilpotents. Each piece carries the exact moving-endpoint action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {T : Scheme.{0}} (z : T ⟶ fullRelation p q I o)

/-- The exact open part of a test carrying the displayed original permutation. -/
def permutationTestOpen (σ : Equiv.Perm I) : T.Opens := by
  let _ := actionGraph_isOpenImmersion e I o σ
  exact z ⁻¹ᵁ (actionGraph e I o σ).opensRange

/-- Distinct permutation pieces are disjoint on the original test. -/
theorem permutationTestOpen_disjoint (σ τ : Equiv.Perm I) (h : σ ≠ τ) :
    Disjoint (permutationTestOpen e I o z σ : Set T) (permutationTestOpen e I o z τ) :=
  (actionGraph_disjoint e I o σ τ h).preimage z

/-- The entire complete-support test is covered by its original permutation pieces. -/
theorem permutationTestOpen_covers
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) (x : T) :
    ∃ σ : Equiv.Perm I, x ∈ permutationTestOpen e I o z σ := by
  obtain ⟨v, hv⟩ := complete_source_range e I o z hz ⟨x, rfl⟩
  obtain ⟨⟨σ, y⟩, rfl⟩ := (sigmaMk (fun _ : Equiv.Perm I ↦ source p q I o)).surjective v
  refine ⟨σ, y, ?_⟩
  have h := congrArg (fun f ↦ f y) (component_relationComparison e I o σ)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm.trans (by simpa only [sigmaMk_mk] using! hv)

/-- On each actual piece the moving endpoint equation holds without reduction. -/
theorem permutationTestOpen_action (σ : Equiv.Perm I) :
    ((permutationTestOpen e I o z σ).ι ≫ z ≫ relationFirst p q I o) ≫
      (action e I o σ).hom =
        (permutationTestOpen e I o z σ).ι ≫ z ≫ relationSecond p q I o := by
  let _ := actionGraph_isOpenImmersion e I o σ
  have hr : Set.range ((permutationTestOpen e I o z σ).ι ≫ z) ⊆
      Set.range (actionGraph e I o σ) := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have h := (factors_actionGraph_iff e I o ((permutationTestOpen e I o z σ).ι ≫ z) σ).mp
    ⟨IsOpenImmersion.lift _ _ hr, IsOpenImmersion.lift_fac _ _ hr⟩
  simpa only [Category.assoc] using h

/-- Each piece retains the actual original arrow, including every coefficient morphism. -/
@[reassoc] theorem permutationTestOpen_arrow (σ : Equiv.Perm I) :
    (permutationTestOpen e I o z σ).ι ≫ z ≫ relationArrow p q I o =
      (permutationTestOpen e I o z σ).ι ≫ z ≫ relationFirst p q I o ≫
        actionArrow I o σ := by
  have h := actionGraph_factor e I o ((permutationTestOpen e I o z σ).ι ≫ z) σ
    (by simpa only [Category.assoc] using permutationTestOpen_action e I o z σ)
  simpa only [Category.assoc, actionGraph_arrow] using
    (congrArg (fun f ↦ f ≫ relationArrow p q I o) h).symm

/-- The finite coproduct map includes the unchanged original open pieces. -/
def permutationTestMap : (∐ fun σ ↦ (permutationTestOpen e I o z σ).toScheme) ⟶ T :=
  Sigma.desc (fun σ ↦ (permutationTestOpen e I o z σ).ι)

instance permutationTestMap_isOpenImmersion : IsOpenImmersion (permutationTestMap e I o z) := by
  apply isOpenImmersion_sigmaDesc
  intro σ τ h
  simpa only [Scheme.Opens.range_ι] using permutationTestOpen_disjoint e I o z σ τ h

/-- The finite scheme partition exhausts every point and every nilpotent of the test. -/
def permutationTestIso
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) :
    (∐ fun σ ↦ (permutationTestOpen e I o z σ).toScheme) ≅ T := by
  have hs : Function.Surjective (permutationTestMap e I o z) := by
    intro x
    obtain ⟨σ, hσ⟩ := permutationTestOpen_covers e I o z hz x
    refine ⟨Sigma.ι (fun τ ↦ (permutationTestOpen e I o z τ).toScheme) σ ⟨x, hσ⟩, ?_⟩
    change (Sigma.ι (fun τ ↦ (permutationTestOpen e I o z τ).toScheme) σ ≫
      permutationTestMap e I o z) ⟨x, hσ⟩ = x
    rw [permutationTestMap, Sigma.ι_comp_desc]
    rfl
  let _ := (isIso_iff_isOpenImmersion_and_surjective (permutationTestMap e I o z)).mpr
    ⟨inferInstance, ⟨hs⟩⟩
  exact asIso (permutationTestMap e I o z)

/-- Each component of the splitting is the original open inclusion. -/
@[reassoc] theorem permutationTestIso_component
    (hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) (σ : Equiv.Perm I) :
    Sigma.ι (fun τ ↦ (permutationTestOpen e I o z τ).toScheme) σ ≫
      (permutationTestIso e I o z hz).hom = (permutationTestOpen e I o z σ).ι :=
  Sigma.ι_comp_desc _ _

end FLT.Mazur.EquivalenceRelationNormalizedFrames
