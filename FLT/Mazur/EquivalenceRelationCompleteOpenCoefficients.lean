/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteTestCoefficients
public import FLT.Mazur.EquivalenceRelationCompleteSourceRestriction
public import FLT.Mazur.FiniteGroupEquivariantOpenBoundary

/-!
# Full original compatibility of coefficients on complete stable opens

Every invariant coefficient on a complete stable open equalizes the entire original
restricted relation. The proof uses the finite partition of that actual scheme,
so it retains nilpotents and does not merely compare values at geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U)
  (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)
local notation "z" => original U.ι U.ι
local notation "r" => SourceRestriction.fst U.ι U.ι
local notation "s" => SourceRestriction.snd U.ι U.ι

/-- The exact moving endpoint equation holds on each piece of the whole restricted relation. -/
theorem completeOpen_piece_action (σ : Equiv.Perm I) :
    ((permutationTestOpen e I o z σ).ι ≫ r) ≫
      (restrictedAction (action e I o) U hU σ).hom =
        (permutationTestOpen e I o z σ).ι ≫ s := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, restrictedAction_hom_ι]
  have h := permutationTestOpen_action e I o z σ
  simpa only [Category.assoc, original_first, original_second] using h

include hc in
/-- Moving invariance implies exact equality on every full original restricted arrow. -/
theorem completeOpen_invariant_equalizes
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    (r).appTop t.val = (s).appTop t.val := by
  have hz : Set.range (z ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o :=
    original_complete_support U.ι U.ι (by simpa only [Scheme.Opens.range_ι] using hc)
  apply permutationTest_sections_ext e I o z hz
  intro σ
  have ht : (restrictedAction (action e I o) U hU σ).hom.appTop t.val = t.val := by
    have h := t.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have h := congrArg (fun a ↦ a.appTop t.val) (completeOpen_piece_action e I o U hU σ)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [ht] at h
  exact h

end FLT.Mazur.EquivalenceRelationNormalizedFrames
