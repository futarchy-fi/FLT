/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteOpenCoefficients

/-!
# Complete equivariant sources retain the full original coefficient equations

A monomorphic source with complete support may be closed and nonreduced.
Moving-invariant coefficients on it equalize every original relation arrow.
The proof works on the actual permutation partition of the entire relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "z" => original j j
local notation "r" => SourceRestriction.fst j j
local notation "s" => SourceRestriction.snd j j

include e hj

/-- Each original permutation piece has the exact induced source action. -/
theorem completeEquivariant_piece_action (σ : Equiv.Perm I) :
    ((permutationTestOpen e I o z σ).ι ≫ r) ≫ (ρ σ).hom =
      (permutationTestOpen e I o z σ).ι ≫ s := by
  apply (cancel_mono j).mp
  rw [Category.assoc, hj]
  have h := permutationTestOpen_action e I o z σ
  simpa only [Category.assoc, original_first, original_second] using h

/-- Only the first endpoint needs complete support; the ambient source may be incomplete. -/
theorem completeEquivariant_invariant_test_of_support
    (t : invariantCoordinates ρ) {T : Scheme.{0}} (w : T ⟶ fullRelation p q I o)
    (u v : T ⟶ S) (hu : u ≫ j = w ≫ relationFirst p q I o)
    (hv : v ≫ j = w ≫ relationSecond p q I o)
    (hz : Set.range (w ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o) : u.appTop t.val = v.appTop t.val := by
  apply permutationTest_sections_ext e I o w hz
  intro σ
  have he : ((permutationTestOpen e I o w σ).ι ≫ u) ≫ (ρ σ).hom =
      (permutationTestOpen e I o w σ).ι ≫ v := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, hj]
    rw [← Category.assoc u, hu, hv]
    simpa only [Category.assoc] using permutationTestOpen_action e I o w σ
  have ht : (ρ σ).hom.appTop t.val = t.val := by
    have h := t.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have h := congrArg (fun a ↦ a.appTop t.val) he
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [ht] at h
  exact h

variable (hc : Set.range j ⊆ completePointLocus (p := p) (q := q) I o)
include hc in
/-- Invariant functions equalize the full original relation, including all nilpotents. -/
theorem completeEquivariant_invariant_equalizes (t : invariantCoordinates ρ) :
    (r).appTop t.val = (s).appTop t.val := by
  apply permutationTest_sections_ext e I o z (original_complete_support j j hc)
  intro σ
  have ht : (ρ σ).hom.appTop t.val = t.val := by
    have h := t.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have h := congrArg (fun a ↦ a.appTop t.val)
    (completeEquivariant_piece_action e I o j ρ hj σ)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [ht] at h
  exact h

include hc in
/-- Arbitrary tests and the unchanged original arrow satisfy the same coefficient equation. -/
theorem completeEquivariant_invariant_test (t : invariantCoordinates ρ)
    {T : Scheme.{0}} (u v : T ⟶ S) (a : T ⟶ D)
    (ha : a ≫ p = u ≫ j ≫ first p q I o)
    (hb : a ≫ q = v ≫ j ≫ first p q I o) : u.appTop t.val = v.appTop t.val := by
  have h := congrArg (fun b ↦ (SourceRestriction.lift j j u v a ha hb).appTop b)
    (completeEquivariant_invariant_equalizes e I o j ρ hj hc t)
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    SourceRestriction.lift_fst, SourceRestriction.lift_snd] using h

end FLT.Mazur.EquivalenceRelationNormalizedFrames
