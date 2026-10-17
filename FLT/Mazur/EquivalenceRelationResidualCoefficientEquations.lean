/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationResidualPermutationOpen

/-!
# The remaining full original equations are exactly the residual equations

Moving invariants already equalize every permutation branch. The residual
open retains all other branches, and testing there detects the full original
equation, scheme-theoretically. No source neighborhood is inferred from its
empty fibers over complete points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An equality on an actual open subscheme gives equality of the original germs. -/
theorem originalGerm_eq_of_open {X : Scheme} (V : X.Opens) {a b : Γ(X, ⊤)}
    (h : V.ι.appTop a = V.ι.appTop b) (x : X) (hx : x ∈ V) :
    X.presheaf.germ ⊤ x (by trivial) a = X.presheaf.germ ⊤ x (by trivial) b := by
  have hx' : x ∈ V.ι ''ᵁ ⊤ := ⟨⟨x, hx⟩, trivial, rfl⟩
  have hh := congrArg ((X.presheaf.germ (V.ι ''ᵁ ⊤) x hx').hom) h
  change (V.ι.appTop ≫ X.presheaf.germ (V.ι ''ᵁ ⊤) x hx') a =
    (V.ι.appTop ≫ X.presheaf.germ (V.ι ''ᵁ ⊤) x hx') b at hh
  rw [Scheme.Opens.ι_appTop, X.presheaf.germ_res] at hh
  exact hh

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j] [S.IsSeparated]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "z" => original j j
local notation "r" => SourceRestriction.fst j j
local notation "s" => SourceRestriction.snd j j
local notation "O" => residualPermutationOpen e I o j ρ hj

/-- The residual piece and the permutation pieces detect full original section equality. -/
theorem residualPermutation_sections_ext {a b : Γ(relation j j, ⊤)}
    (hO : (O).ι.appTop a = (O).ι.appTop b)
    (hσ : ∀ σ : Equiv.Perm I,
      (permutationTestOpen e I o z σ).ι.appTop a =
        (permutationTestOpen e I o z σ).ι.appTop b) : a = b := by
  apply TopCat.Presheaf.section_ext (relation j j).sheaf
  intro x _
  obtain hx | ⟨σ, hx⟩ := residualPermutationOpen_covers e I o j ρ hj x
  · exact originalGerm_eq_of_open O hO x hx
  · exact originalGerm_eq_of_open _ (hσ σ) x hx

include hj in
omit [S.IsSeparated] in
/-- Every original permutation branch equalizes a moving-invariant coefficient. -/
theorem permutationPiece_invariant_equalizes (t : invariantCoordinates ρ) (σ : Equiv.Perm I) :
    ((permutationTestOpen e I o z σ).ι ≫ (r)).appTop t.val =
      ((permutationTestOpen e I o z σ).ι ≫ (s)).appTop t.val := by
  have ht : (ρ σ).hom.appTop t.val = t.val := by
    have h := t.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have h := congrArg (fun a ↦ a.appTop t.val)
    (completeEquivariant_piece_action e I o j ρ hj σ)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h ⊢
  rw [ht] at h
  exact h

/-- A moving invariant satisfies the entire original relation iff it satisfies the residual part. -/
theorem invariant_equalizes_iff_residual (t : invariantCoordinates ρ) :
    (r).appTop t.val = (s).appTop t.val ↔
      ((O).ι ≫ (r)).appTop t.val = ((O).ι ≫ (s)).appTop t.val := by
  constructor
  · intro h
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun a ↦ (O).ι.appTop a) h
  · intro h
    apply residualPermutation_sections_ext e I o j ρ hj
    · simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
    · intro σ
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
        permutationPiece_invariant_equalizes e I o j ρ hj t σ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
