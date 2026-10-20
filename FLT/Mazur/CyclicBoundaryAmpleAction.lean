/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryRelabelSubgroup
public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# The common finite action on the ample boundary open

Actual compatible subgroup isomorphisms preserve ampleness on every scheme test.
The resulting automorphisms retain the original ambient parameter action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
local notation "P" => cyclicFaithfulParameter E.group n
local notation "H" => faithfulUniversalSubgroup E n
local notation "ι" => Scheme.Opens.ι (ampleParameterOpen E n)

/-- Relabeling preserves each actual pulled-back subgroup and its original full curve. -/
def faithfulRelabeledTestIso {T : Scheme} (u : T ⟶ (P).left) (e : RelabelGroup n) :
    CompatibleIso ((H).baseChange (u ≫ (faithfulRelabel E.group n e).left))
      ((H).baseChange u) :=
  ((H).compatibleBaseChangeComp (faithfulRelabel E.group n e).left u).trans
    ((faithfulRelabelSubgroupIso E n e).baseChange u)

/-- Ampleness on every test is invariant under the original finite relabeling. -/
theorem ampleParameter_action_criterion {T : Scheme} (u : T ⟶ (P).left)
    (e : RelabelGroup n) :
    Set.range (u ≫ (faithfulRelabel E.group n e).left) ⊆ ampleParameterOpen E n ↔
      Set.range u ⊆ ampleParameterOpen E n :=
  ((H).isAmple_baseChange_iff_range (faithfulUniversalSubgroup_cartier E n).1
    (u ≫ (faithfulRelabel E.group n e).left)).symm.trans
      ((faithfulRelabeledTestIso E n u e).isAmple_iff.trans
        ((H).isAmple_baseChange_iff_range (faithfulUniversalSubgroup_cartier E n).1 u))

/-- Restrict the finite relabeling to the actual ample open. -/
def ampleRelabel (e : RelabelGroup n) : ampleParameter E n ⟶ ampleParameter E n :=
  (H).ampleOpenLift (faithfulUniversalSubgroup_cartier E n).1
    ((ι) ≫ (faithfulRelabel E.group n e).left)
    ((faithfulRelabeledTestIso E n (ι) e).isAmple_iff.mpr
      ((H).ampleOpen_isAmple (faithfulUniversalSubgroup_cartier E n).1))

/-- The restriction retains the original faithful parameter. -/
@[reassoc] theorem ampleRelabel_inclusion (e : RelabelGroup n) :
    ampleRelabel E n e ≫ (ι) = (ι) ≫ (faithfulRelabel E.group n e).left :=
  (H).ampleOpenLift_inclusion _ _ _

/-- The ample restriction retains all original auxiliary and cyclic labels. -/
@[reassoc] theorem ampleRelabel_parameter (e : RelabelGroup n) :
    ampleRelabel E n e ≫ ampleParameterInclusion E n =
      ampleParameterInclusion E n ≫ (schemeAction E.group n e).hom := by
  change ampleRelabel E n e ≫ (ι) ≫ (cyclicFaithfulInclusion E.group n).left = _
  rw [ampleRelabel_inclusion_assoc]
  have h := congrArg Over.Hom.left (faithfulRelabel_inclusion E.group n e)
  exact congrArg (fun f ↦ (ι) ≫ f) h

/-- Identity acts identically on the actual ample open. -/
@[simp] theorem ampleRelabel_one : ampleRelabel E n 1 = 𝟙 _ := by
  apply (cancel_mono (ι)).mp
  rw [ampleRelabel_inclusion, faithfulRelabel_one, Over.id_left,
    Category.comp_id, Category.id_comp]

/-- The ample restriction obeys the original left-action multiplication law. -/
theorem ampleRelabel_mul (e f : RelabelGroup n) :
    ampleRelabel E n (e * f) = ampleRelabel E n f ≫ ampleRelabel E n e := by
  apply (cancel_mono (ι)).mp
  rw [ampleRelabel_inclusion, Category.assoc, ampleRelabel_inclusion,
    ampleRelabel_inclusion_assoc, faithfulRelabel_mul, Over.comp_left]

/-- The common finite group acts on the ample parameter by actual scheme automorphisms. -/
def ampleAction : RelabelGroup n →* Aut (ampleParameter E n) where
  toFun e :=
    { hom := ampleRelabel E n e
      inv := ampleRelabel E n e⁻¹
      hom_inv_id := by rw [← ampleRelabel_mul, inv_mul_cancel, ampleRelabel_one]
      inv_hom_id := by rw [← ampleRelabel_mul, mul_inv_cancel, ampleRelabel_one] }
  map_one' := by apply Aut.ext; exact ampleRelabel_one E n
  map_mul' e f := by apply Aut.ext; exact ampleRelabel_mul E n e f

end FLT.Mazur.CyclicBoundaryParameter
