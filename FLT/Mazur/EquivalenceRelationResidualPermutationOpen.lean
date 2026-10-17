/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRestrictedActionGraphs

/-!
# The actual residual branches outside all original permutation graphs

On a separated equivariant source, the finite union of permutation pieces is
clopen. Its complement is an actual open subscheme of the full original
relation, with no complete first-endpoint fibers. The complement is retained;
its image is not presumed closed in the source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j] [S.IsSeparated]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "z" => original j j
local notation "r" => SourceRestriction.fst j j

/-- The finite union of all actual permutation pieces in the entire restricted relation. -/
def restrictedPermutationOpen : (relation j j).Opens :=
  ⨆ σ : Equiv.Perm I, permutationTestOpen e I o z σ

include hj in
/-- The whole permutation part is closed, by finiteness of the permutation group. -/
theorem restrictedPermutationOpen_isClosed :
    IsClosed (restrictedPermutationOpen e I o j : Set (relation j j)) := by
  rw [restrictedPermutationOpen, TopologicalSpace.Opens.coe_iSup]
  exact isClosed_iUnion_of_finite fun σ ↦ permutationTestOpen_isClosed e I o j ρ hj σ

/-- The open complement retains every nonpermutation original relation branch. -/
def residualPermutationOpen : (relation j j).Opens :=
  ⟨(restrictedPermutationOpen e I o j : Set (relation j j))ᶜ,
    (restrictedPermutationOpen_isClosed e I o j ρ hj).isOpen_compl⟩

/-- Membership in the residual open excludes every individual original permutation. -/
theorem mem_residualPermutationOpen (x : relation j j) :
    x ∈ residualPermutationOpen e I o j ρ hj ↔
      ∀ σ : Equiv.Perm I, x ∉ permutationTestOpen e I o z σ := by
  simp [residualPermutationOpen, restrictedPermutationOpen, TopologicalSpace.Opens.coe_iSup]


/-- Each original arrow lies either in the residual open or in an actual permutation piece. -/
theorem residualPermutationOpen_covers (x : relation j j) :
    x ∈ residualPermutationOpen e I o j ρ hj ∨
      ∃ σ : Equiv.Perm I, x ∈ permutationTestOpen e I o z σ := by
  classical
  rw [mem_residualPermutationOpen]
  exact (Classical.em (∃ σ, x ∈ permutationTestOpen e I o z σ)).symm.imp_left
    (by simpa only [not_exists] using id)

omit [Mono j] [S.IsSeparated] in
/-- A complete first endpoint forces an actual original arrow into a permutation piece. -/
theorem complete_first_mem_permutation (x : relation j j)
    (hx : ((r) ≫ j) x ∈ completePointLocus (p := p) (q := q) I o) :
    ∃ σ : Equiv.Perm I, x ∈ permutationTestOpen e I o z σ := by
  let v := (relation j j).fromSpecResidueField x
  have hv : Set.range ((v ≫ z) ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o := by
    rintro _ ⟨y, rfl⟩
    simpa only [Category.assoc, original_first, Scheme.Hom.comp_apply,
      v, Scheme.fromSpecResidueField_apply] using hx
  obtain ⟨σ, hσ⟩ := permutationTestOpen_covers e I o (v ≫ z) hv default
  refine ⟨σ, ?_⟩
  change z x ∈ Set.range (actionGraph e I o σ)
  change z (v default) ∈ Set.range (actionGraph e I o σ) at hσ
  simpa only [v, Scheme.fromSpecResidueField_apply] using hσ

/-- No residual arrow lies over any complete original first endpoint. -/
theorem residualPermutationOpen_first_incomplete
    (x : (residualPermutationOpen e I o j ρ hj).toScheme) :
    ((residualPermutationOpen e I o j ρ hj).ι ≫ (r) ≫ j) x ∉
      completePointLocus (p := p) (q := q) I o := by
  intro hx
  obtain ⟨σ, hσ⟩ := complete_first_mem_permutation e I o j x.val hx
  exact (mem_residualPermutationOpen e I o j ρ hj x.val).mp x.property σ hσ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
