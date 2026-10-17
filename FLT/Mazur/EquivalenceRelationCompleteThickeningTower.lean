/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteThickeningAction

/-!
# Equivariant transition maps for the complete infinitesimal sources

Every lower-order stage embeds in every higher-order stage by the actual ideal
power inclusion. These maps compose and commute with the moving action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)

/-- Higher powers of the original complete ideal are smaller as ideal sheaves. -/
theorem completeSupportIdeal_pow_antitone {m n : ℕ} (h : m ≤ n) :
    completeSupportIdeal (p := p) (q := q) I o ^ (n + 1) ≤
      completeSupportIdeal (p := p) (q := q) I o ^ (m + 1) := by
  intro U
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)

/-- The canonical scheme transition retains the entire power-quotient structure. -/
def completeThickeningTransition {m n : ℕ} (h : m ≤ n) :
    completeThickening (p := p) (q := q) I o m ⟶
      completeThickening (p := p) (q := q) I o n :=
  Scheme.IdealSheafData.inclusion (completeSupportIdeal_pow_antitone I o h)

/-- The transition is a closed immersion of actual infinitesimal sources. -/
instance completeThickeningTransition_isClosedImmersion {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (completeThickeningTransition (p := p) (q := q) I o h) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.inclusion (completeSupportIdeal_pow_antitone I o h)))

/-- Transitions preserve the original source inclusion. -/
@[reassoc] theorem completeThickeningTransition_inclusion {m n : ℕ} (h : m ≤ n) :
    completeThickeningTransition (p := p) (q := q) I o h ≫
      completeThickeningInclusion I o n = completeThickeningInclusion I o m :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The scheme transitions satisfy the full cocycle identity. -/
@[reassoc] theorem completeThickeningTransition_comp {l m n : ℕ}
    (h : l ≤ m) (h' : m ≤ n) :
    completeThickeningTransition (p := p) (q := q) I o h ≫
        completeThickeningTransition I o h' = completeThickeningTransition I o (h.trans h') := by
  apply (cancel_mono (completeThickeningInclusion (p := p) (q := q) I o n)).mp
  rw [Category.assoc, completeThickeningTransition_inclusion,
    completeThickeningTransition_inclusion, completeThickeningTransition_inclusion]

/-- A transition at the same order is the identity. -/
theorem completeThickeningTransition_refl (n : ℕ) :
    completeThickeningTransition (p := p) (q := q) I o (le_refl n) = 𝟙 _ := by
  apply (cancel_mono (completeThickeningInclusion (p := p) (q := q) I o n)).mp
  rw [completeThickeningTransition_inclusion, Category.id_comp]

variable (e : CategoryTheory.EquivalenceRelation p q)

/-- The constructed stage inclusions are equivariant for every moving permutation. -/
@[reassoc] theorem completeThickeningTransition_equivariant {m n : ℕ} (h : m ≤ n)
    (σ : Equiv.Perm I) :
    (completeThickeningAction e I o m σ).hom ≫ completeThickeningTransition I o h =
      completeThickeningTransition I o h ≫ (completeThickeningAction e I o n σ).hom := by
  apply (cancel_mono (completeThickeningInclusion (p := p) (q := q) I o n)).mp
  change (completeThickeningActionMap e I o m σ ≫ _) ≫ _ =
    (_ ≫ completeThickeningActionMap e I o n σ) ≫ _
  rw [Category.assoc, completeThickeningTransition_inclusion,
    completeThickeningActionMap_inclusion, Category.assoc,
    completeThickeningActionMap_inclusion, completeThickeningTransition_inclusion_assoc]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
