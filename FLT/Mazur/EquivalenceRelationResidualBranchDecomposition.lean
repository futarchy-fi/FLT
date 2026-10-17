/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationResidualCoefficientEquations

/-!
# A scheme decomposition retaining every residual original branch

The full original relation is the disjoint coproduct of its residual open and
its finite permutation pieces. The latter are actual copies of the original
source, while the residual component is left unchanged. Global coefficients
therefore decompose as a product, including all nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
local notation "s" => SourceRestriction.snd j j

omit [S.IsSeparated] in
/-- Every permutation piece is an actual copy of the entire original equivariant source. -/
def restrictedPermutationPieceIso (σ : Equiv.Perm I) :
    S ≅ (permutationTestOpen e I o z σ).toScheme := by
  let V := permutationTestOpen e I o z σ
  let g := restrictedActionGraph e I o j ρ hj σ
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (restrictedActionGraph_range e I o j ρ hj σ).le
  let a := IsOpenImmersion.lift V.ι g hr
  have ha : a ≫ V.ι = g := IsOpenImmersion.lift_fac V.ι g hr
  refine ⟨a, V.ι ≫ (r), ?_, ?_⟩
  · rw [← Category.assoc, ha]
    exact restrictedActionGraph_first e I o j ρ hj σ
  · apply (cancel_mono V.ι).mp
    rw [Category.id_comp, Category.assoc, ha]
    apply SourceRestriction.hom_ext j j e
    · rw [Category.assoc, restrictedActionGraph_first, Category.comp_id]
    · rw [Category.assoc, restrictedActionGraph_second]
      exact completeEquivariant_piece_action e I o j ρ hj σ

/-- The residual piece is indexed separately from every original permutation piece. -/
def residualBranchOpen : Option (Equiv.Perm I) → (relation j j).Opens
  | none => residualPermutationOpen e I o j ρ hj
  | some σ => permutationTestOpen e I o z σ

/-- The unchanged residual and permutation pieces are pairwise disjoint. -/
theorem residualBranchOpen_disjoint (a b : Option (Equiv.Perm I)) (h : a ≠ b) :
    Disjoint (residualBranchOpen e I o j ρ hj a : Set (relation j j))
      (residualBranchOpen e I o j ρ hj b : Set (relation j j)) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  cases a with
  | none =>
    cases b with
    | none => exact h rfl
    | some σ => exact (mem_residualPermutationOpen e I o j ρ hj x).mp ha σ hb
  | some σ =>
    cases b with
    | none => exact (mem_residualPermutationOpen e I o j ρ hj x).mp hb σ ha
    | some τ =>
      exact Set.disjoint_left.mp (permutationTestOpen_disjoint e I o z σ τ
        (fun he ↦ h (congrArg some he))) ha hb

/-- The actual coproduct map retains every original open inclusion. -/
def residualBranchMap :
    (∐ fun a ↦ (residualBranchOpen e I o j ρ hj a).toScheme) ⟶ relation j j :=
  Sigma.desc fun a ↦ (residualBranchOpen e I o j ρ hj a).ι

instance residualBranchMap_open : IsOpenImmersion (residualBranchMap e I o j ρ hj) := by
  apply isOpenImmersion_sigmaDesc
  intro a b h
  simpa only [Scheme.Opens.range_ι] using residualBranchOpen_disjoint e I o j ρ hj a b h

/-- This coproduct covers the full original relation, with no support reduction. -/
def residualBranchIso :
    (∐ fun a ↦ (residualBranchOpen e I o j ρ hj a).toScheme) ≅ relation j j := by
  have hs : Function.Surjective (residualBranchMap e I o j ρ hj) := by
    intro x
    have hx : ∃ a, x ∈ residualBranchOpen e I o j ρ hj a := by
      obtain hx | ⟨σ, hx⟩ := residualPermutationOpen_covers e I o j ρ hj x
      · exact ⟨none, hx⟩
      · exact ⟨some σ, hx⟩
    obtain ⟨a, ha⟩ := hx
    refine ⟨Sigma.ι (fun b ↦ (residualBranchOpen e I o j ρ hj b).toScheme) a ⟨x, ha⟩, ?_⟩
    change (Sigma.ι _ a ≫ residualBranchMap e I o j ρ hj) ⟨x, ha⟩ = x
    rw [residualBranchMap, Sigma.ι_comp_desc]
    rfl
  let _ := (isIso_iff_isOpenImmersion_and_surjective
    (residualBranchMap e I o j ρ hj)).mpr ⟨inferInstance, ⟨hs⟩⟩
  exact asIso (residualBranchMap e I o j ρ hj)

/-- The decomposition keeps each original branch inclusion as an exact scheme morphism. -/
@[reassoc] theorem residualBranchIso_component (a : Option (Equiv.Perm I)) :
    Sigma.ι _ a ≫ (residualBranchIso e I o j ρ hj).hom =
      (residualBranchOpen e I o j ρ hj a).ι := Sigma.ι_comp_desc _ _

/-- The full coefficient ring is the product of the residual and original permutation rings. -/
def residualBranchSectionsIso : Γ(relation j j, ⊤) ≅
    CommRingCat.of (∀ a, Γ((residualBranchOpen e I o j ρ hj a).toScheme, ⊤)) :=
  Scheme.Γ.mapIso (residualBranchIso e I o j ρ hj).op ≪≫ SchemeCoproductSections.iso _

/-- Every coefficient projection is the actual restriction to the corresponding branch. -/
theorem residualBranchSectionsIso_apply (t : Γ(relation j j, ⊤))
    (a : Option (Equiv.Perm I)) :
    (residualBranchSectionsIso e I o j ρ hj).hom t a =
      (residualBranchOpen e I o j ρ hj a).ι.appTop t := by
  change (SchemeCoproductSections.iso _).hom
    ((residualBranchIso e I o j ρ hj).hom.appTop t) a = _
  rw [SchemeCoproductSections.iso_apply]
  change (((residualBranchIso e I o j ρ hj).hom.appTop ≫
    (Sigma.ι (fun b ↦ (residualBranchOpen e I o j ρ hj b).toScheme) a).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, residualBranchIso_component]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
