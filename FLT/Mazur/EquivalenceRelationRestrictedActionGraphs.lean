/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteEquivariantCoefficients

/-!
# Closed action sections on a separated original source

An equivariant monomorphic source retains actual permutation sections of its
full original relation. A separated source makes each section closed as well
as open. No finiteness of the full original relation is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "r" => SourceRestriction.fst j j
local notation "s" => SourceRestriction.snd j j
local notation "z" => original j j

include e in
omit [Etale p] [Mono j] in
/-- The full original relation embeds monomorphically in the two-endpoint product. -/
theorem restrictedEndpointPair_mono : Mono (pullback.lift (r) (s)
    (show (r) ≫ terminal.from S = (s) ≫ terminal.from S from terminal.hom_ext _ _)) := by
  constructor
  intro T u v h
  apply SourceRestriction.hom_ext j j e
  · simpa only [Category.assoc, pullback.lift_fst] using congrArg (fun a ↦ a ≫ pullback.fst _ _) h
  · simpa only [Category.assoc, pullback.lift_snd] using congrArg (fun a ↦ a ≫ pullback.snd _ _) h

include e in
omit [Etale p] [Mono j] in
/-- Separatedness of the original source suffices for the full restricted first projection. -/
theorem restrictedFirst_separated [S.IsSeparated] : IsSeparated r := by
  let _ := restrictedEndpointPair_mono e I o j
  have : IsSeparated (pullback.lift (r) (s)
      (show (r) ≫ terminal.from S = (s) ≫ terminal.from S from terminal.hom_ext _ _) ≫
      pullback.fst _ _) := inferInstance
  rwa [pullback.lift_fst] at this

/-- The original action arrow lifts with both restricted source endpoints intact. -/
def restrictedActionGraph (σ : Equiv.Perm I) : S ⟶ relation j j :=
  SourceRestriction.lift j j (𝟙 S) (ρ σ).hom (j ≫ actionArrow I o σ)
    (by rw [Category.assoc, actionArrow_first, Category.id_comp])
    (by rw [Category.assoc, actionArrow_second, ← Category.assoc, ← hj, Category.assoc])

omit [Etale p] [Mono j] in
/-- Each restricted action graph is a section of the full original first endpoint. -/
@[reassoc] theorem restrictedActionGraph_first (σ : Equiv.Perm I) :
    restrictedActionGraph e I o j ρ hj σ ≫ (r) = 𝟙 S :=
  SourceRestriction.lift_fst _ _ _ _ _ _ _

omit [Etale p] [Mono j] in
/-- The second endpoint is precisely the supplied equivariant action. -/
@[reassoc] theorem restrictedActionGraph_second (σ : Equiv.Perm I) :
    restrictedActionGraph e I o j ρ hj σ ≫ (s) = (ρ σ).hom :=
  SourceRestriction.lift_snd _ _ _ _ _ _ _

omit [Etale p] [Mono j] in
/-- The section retains the actual full original permutation graph. -/
@[reassoc] theorem restrictedActionGraph_original (σ : Equiv.Perm I) :
    restrictedActionGraph e I o j ρ hj σ ≫ (z) = j ≫ actionGraph e I o σ := by
  apply relation_hom_ext p q I o e
  · rw [Category.assoc, original_first, restrictedActionGraph_first_assoc,
      Category.assoc, actionGraph_first, Category.comp_id]
  · rw [Category.assoc, original_second, restrictedActionGraph_second_assoc,
      hj, Category.assoc, actionGraph_second]

omit [Etale p] [Mono j] in
/-- The actual restricted graph is closed when its source is separated. -/
theorem restrictedActionGraph_closed [S.IsSeparated] (σ : Equiv.Perm I) :
    IsClosedImmersion (restrictedActionGraph e I o j ρ hj σ) := by
  let _ := restrictedFirst_separated e I o j
  exact UnramifiedSectionImmersion.isClosedImmersion (r) _
    (restrictedActionGraph_first e I o j ρ hj σ)

/-- Its image is exactly the corresponding original permutation test piece. -/
theorem restrictedActionGraph_range (σ : Equiv.Perm I) :
    Set.range (restrictedActionGraph e I o j ρ hj σ) =
      (permutationTestOpen e I o z σ : Set (relation j j)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨j x, congrArg (fun a ↦ a x)
      (restrictedActionGraph_original e I o j ρ hj σ).symm⟩
  · intro x hx
    let v := (permutationTestOpen e I o z σ).ι
    have h : (v ≫ (r)) ≫ restrictedActionGraph e I o j ρ hj σ = v := by
      apply SourceRestriction.hom_ext j j e
      · rw [Category.assoc, restrictedActionGraph_first, Category.comp_id]
      · rw [Category.assoc, restrictedActionGraph_second]
        exact completeEquivariant_piece_action e I o j ρ hj σ
    exact ⟨(r) x, congrArg (fun a ↦ a ⟨x, hx⟩) h⟩

include hj in
/-- Every original permutation piece is clopen, including over incomplete source points. -/
theorem permutationTestOpen_isClosed [S.IsSeparated] (σ : Equiv.Perm I) :
    IsClosed (permutationTestOpen e I o z σ : Set (relation j j)) := by
  let _ := restrictedActionGraph_closed e I o j ρ hj σ
  rw [← restrictedActionGraph_range e I o j ρ hj σ]
  exact (restrictedActionGraph e I o j ρ hj σ).isClosedEmbedding.isClosed_range

end FLT.Mazur.EquivalenceRelationNormalizedFrames
