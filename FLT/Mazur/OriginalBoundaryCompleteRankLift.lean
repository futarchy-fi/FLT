/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryCompleteResidualIdeal

/-!
# Full original boundary lifts from complete rank corrections

The complete finite family detects the original residual radical, so a shared
correction on all its charts gives a powered lift on the entire boundary.
The output is an original invariant numerator, not merely a chartwise one.
Only one prescribed pair of orders is needed; no inverse-limit claim is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A}
  [IsSeparated p] [Etale p] [QuasiCompact p] [IsAffine A]
  [TopologicalSpace.NoetherianSpace A]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
  [IsAffine S] (g : A ⟶ S) (hg : p ≫ g = q ≫ g) [IsSeparated g]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "R" => compatibleFunctions p q
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J
local notation "L" => originalBoundaryLiftIdeal (p := p) (q := q) J t.val

include e hg in
/-- A complete rectangle's corrections lie in the radical of the actual full lift ideal. -/
theorem exists_originalBoundary_complete_rank_lift_radical :
    ∃ N : ℕ, ∀ r s : ℕ,
      originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s ≤ (L).radical := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_residual_radical (p := p) (q := q) J
  have hH : (H).radical ≤ (L).radical := Ideal.radical_le_radical_iff.mpr
    (originalBoundaryResidualIdeal_le_lift_radical J e hJ g hg t)
  refine ⟨N, fun r s ↦ ?_⟩
  exact Ideal.le_radical.trans ((le_of_eq (hN r s)).trans hH)

include e hg in
/-- Complete rank corrections construct equality on the whole original boundary after a power. -/
theorem exists_originalBoundary_complete_rank_full_lift :
    ∃ N : ℕ, ∀ (r s : ℕ) (a : R),
      a ∈ originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s →
      ∃ (k : ℕ) (u : R),
        J.subschemeι.appTop u.val = J.subschemeι.appTop (a ^ k).val * t.val := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_rank_lift_radical J e hJ g hg t
  refine ⟨N, fun r s a ha ↦ ?_⟩
  obtain ⟨k, u, hu⟩ := hN r s ha
  exact ⟨k, u, hu⟩

include e hg in
/-- A whole finitely generated scalar ideal has one power lifting every one of its elements. -/
theorem exists_originalBoundary_complete_rank_ideal_lifts :
    ∃ N : ℕ, ∀ (r s : ℕ) (Q : Ideal R) (_ : Q.FG),
      Q ≤ (originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s).radical →
      ∃ k : ℕ, Q ^ k ≤ L := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_rank_lift_radical J e hJ g hg t
  refine ⟨N, fun r s Q hfg hQ ↦ ?_⟩
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ hfg
  exact hQ.trans (Ideal.radical_le_radical_iff.mpr (hN r s))

end FLT.Mazur.EquivalenceRelationOrderedFrames
