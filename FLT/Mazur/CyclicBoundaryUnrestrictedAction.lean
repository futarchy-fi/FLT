/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedRelabelCriterion

/-!
# The common finite action on the unrestricted closed boundary locus

Invariant full orbit equations lift the ambient action uniquely through the
actual closed immersion. Identity and composition hold as scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "B" => parameter E.group n
local notation "L" => unrestrictedMultiplicationLocus E n
local notation "i" => unrestrictedMultiplicationLocusInclusion E n

/-- The actual common relabeling lifts through the full closed multiplication locus. -/
def unrestrictedRelabel (e : RelabelGroup n) : L ⟶ L :=
  ((unrestrictedTestLocus_action_iff E n ((i) ≫ (B).hom)
    (Over.homMk (i) rfl) e).mpr ⟨𝟙 _, Category.id_comp _⟩).choose

/-- The lifted action retains every original parameter coordinate. -/
@[reassoc] theorem unrestrictedRelabel_inclusion (e : RelabelGroup n) :
    unrestrictedRelabel E n e ≫ (i) = (i) ≫ (schemeAction E.group n e).hom :=
  ((unrestrictedTestLocus_action_iff E n ((i) ≫ (B).hom)
    (Over.homMk (i) rfl) e).mpr ⟨𝟙 _, Category.id_comp _⟩).choose_spec

/-- The complete coefficient map is unchanged by the closed-locus action. -/
@[reassoc] theorem unrestrictedRelabel_base (e : RelabelGroup n) :
    unrestrictedRelabel E n e ≫ (i) ≫ (B).hom = (i) ≫ (B).hom := by
  rw [unrestrictedRelabel_inclusion_assoc, action_base]

/-- Identity relabeling is the identity on the full closed scheme. -/
@[simp] theorem unrestrictedRelabel_one : unrestrictedRelabel E n 1 = 𝟙 _ := by
  apply (cancel_mono (i)).mp
  rw [unrestrictedRelabel_inclusion, map_one, Category.id_comp]
  exact Category.comp_id _

/-- Composition retains the same left-action convention as the original parameter. -/
theorem unrestrictedRelabel_mul (e f : RelabelGroup n) :
    unrestrictedRelabel E n (e * f) = unrestrictedRelabel E n f ≫
      unrestrictedRelabel E n e := by
  apply (cancel_mono (i)).mp
  rw [unrestrictedRelabel_inclusion, Category.assoc, unrestrictedRelabel_inclusion,
    unrestrictedRelabel_inclusion_assoc, map_mul]
  rfl

/-- The common finite group acts on the full closed locus, including non-faithful markings. -/
def unrestrictedAction : RelabelGroup n →* Aut (L) where
  toFun e :=
    { hom := unrestrictedRelabel E n e
      inv := unrestrictedRelabel E n e⁻¹
      hom_inv_id := by rw [← unrestrictedRelabel_mul, inv_mul_cancel, unrestrictedRelabel_one]
      inv_hom_id := by rw [← unrestrictedRelabel_mul, mul_inv_cancel, unrestrictedRelabel_one] }
  map_one' := by apply Aut.ext; exact unrestrictedRelabel_one E n
  map_mul' e f := by apply Aut.ext; exact unrestrictedRelabel_mul E n e f

end FLT.Mazur.CyclicBoundaryParameter
