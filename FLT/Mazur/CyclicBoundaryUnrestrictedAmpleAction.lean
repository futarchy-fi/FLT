/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedRelabelSubgroup
public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleModuli
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# The common finite action on the unrestricted ample chart

Full subgroup comparisons preserve ampleness on arbitrary scheme tests.
The restricted action retains the closed parameter and all original labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => unrestrictedLocusSubgroup E n
local notation "hI" => And.left (And.left (And.right (unrestrictedLocusGenerator_cartier E n)))
local notation "ι" => Scheme.Opens.ι (unrestrictedAmpleOpen E n)

/-- Every original test retains its entire subgroup under unrestricted relabeling. -/
def unrestrictedRelabeledTestIso {T : Scheme}
    (u : T ⟶ unrestrictedMultiplicationLocus E n) (e : RelabelGroup n) :
    CompatibleIso ((H).baseChange u) ((H).baseChange (u ≫ unrestrictedRelabel E n e)) :=
  ((unrestrictedRelabelSubgroupIso E n e).baseChange u).trans
    ((H).compatibleBaseChangeComp (unrestrictedRelabel E n e) u).symm

/-- Ampleness is invariant as an actual open condition on every test scheme. -/
theorem unrestrictedAmple_action_criterion {T : Scheme}
    (u : T ⟶ unrestrictedMultiplicationLocus E n) (e : RelabelGroup n) :
    Set.range (u ≫ unrestrictedRelabel E n e) ⊆ unrestrictedAmpleOpen E n ↔
      Set.range u ⊆ unrestrictedAmpleOpen E n :=
  ((H).isAmple_baseChange_iff_range (hI) (u ≫ unrestrictedRelabel E n e)).symm.trans
    ((unrestrictedRelabeledTestIso E n u e).isAmple_iff.symm.trans
      ((H).isAmple_baseChange_iff_range (hI) u))

/-- The actual unrestricted action restricts to the ample open. -/
def unrestrictedAmpleRelabel (e : RelabelGroup n) :
    (unrestrictedAmpleOpen E n).toScheme ⟶ (unrestrictedAmpleOpen E n).toScheme :=
  (H).ampleOpenLift (hI) ((ι) ≫ unrestrictedRelabel E n e)
    ((unrestrictedRelabeledTestIso E n (ι) e).isAmple ((H).ampleOpen_isAmple (hI)))

/-- Restriction retains the complete original closed-locus action. -/
@[reassoc] theorem unrestrictedAmpleRelabel_inclusion (e : RelabelGroup n) :
    unrestrictedAmpleRelabel E n e ≫ (ι) = (ι) ≫ unrestrictedRelabel E n e :=
  (H).ampleOpenLift_inclusion _ _ _

/-- Identity relabeling is the identity on the actual ample scheme. -/
@[simp] theorem unrestrictedAmpleRelabel_one : unrestrictedAmpleRelabel E n 1 = 𝟙 _ := by
  apply (cancel_mono (ι)).mp
  rw [unrestrictedAmpleRelabel_inclusion, unrestrictedRelabel_one,
    Category.comp_id, Category.id_comp]

/-- The ample action follows the same composition convention as the closed and ambient actions. -/
theorem unrestrictedAmpleRelabel_mul (e f : RelabelGroup n) :
    unrestrictedAmpleRelabel E n (e * f) =
      unrestrictedAmpleRelabel E n f ≫ unrestrictedAmpleRelabel E n e := by
  apply (cancel_mono (ι)).mp
  rw [unrestrictedAmpleRelabel_inclusion, Category.assoc, unrestrictedAmpleRelabel_inclusion,
    unrestrictedAmpleRelabel_inclusion_assoc, unrestrictedRelabel_mul]

/-- The common finite group acts on the unrestricted ample scheme by automorphisms. -/
def unrestrictedAmpleAction : RelabelGroup n →* Aut (unrestrictedAmpleOpen E n).toScheme where
  toFun e :=
    { hom := unrestrictedAmpleRelabel E n e
      inv := unrestrictedAmpleRelabel E n e⁻¹
      hom_inv_id := by
        rw [← unrestrictedAmpleRelabel_mul, inv_mul_cancel, unrestrictedAmpleRelabel_one]
      inv_hom_id := by
        rw [← unrestrictedAmpleRelabel_mul, mul_inv_cancel, unrestrictedAmpleRelabel_one] }
  map_one' := by apply Aut.ext; exact unrestrictedAmpleRelabel_one E n
  map_mul' e f := by apply Aut.ext; exact unrestrictedAmpleRelabel_mul E n e f

end FLT.Mazur.CyclicBoundaryParameter
