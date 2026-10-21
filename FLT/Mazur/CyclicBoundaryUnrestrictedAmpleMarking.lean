/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleLift

/-!
# The unrestricted ample lift retains all markings and the original generator

The open restriction keeps the full group labels and an actual subgroup
generator. Its comparison preserves those sections on arbitrary scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]

/-- Every full boundary label restricts to the actual ample universal curve. -/
def unrestrictedAmpleLabel (j : Label n) :
    𝟙_ (Over (unrestrictedAmpleOpen E n).toScheme) ⟶
      (unrestrictedAmpleLevel E n).val.1.group :=
  pullSection (unrestrictedAmpleOpen E n).ι (unrestrictedLocusLabel E n j)

/-- The actual universal generator on the ample open, including repeated orbit labels. -/
def unrestrictedAmpleGenerator : 𝟙_ (Over (unrestrictedAmpleOpen E n).toScheme) ⟶
    (unrestrictedAmpleLevel E n).val.2.carrier :=
  pullSection (unrestrictedAmpleOpen E n).ι (unrestrictedLocusGenerator E n)

/-- Restricting to the ample open preserves the full Cartier generator condition. -/
theorem unrestrictedAmpleGenerator_cartier :
    (unrestrictedAmpleLevel E n).val.2.IsCartierGenerator (unrestrictedAmpleGenerator E n) :=
  (unrestrictedLocusGenerator_cartier E n).baseChange _ _

variable {F : GeneralizedEllipticCurve T} (H : F.FiniteSubgroup n)
  (k : T ⟶ unrestrictedMultiplicationLocus E n)
  (d : CompatibleIso H ((unrestrictedLocusSubgroup E n).baseChange k)) (ha : H.IsAmple)

/-- Every original compatible group label survives the actual lift to the ample open. -/
theorem unrestrictedAmpleLiftSubgroupIso_label (j : Label n)
    (p : 𝟙_ (Over T) ⟶ F.group)
    (hp : p ≫ d.curve.hom.group = pullSection k (unrestrictedLocusLabel E n j)) :
    p ≫ (unrestrictedAmpleLiftSubgroupIso E n H k d ha).curve.hom.group =
      pullSection (unrestrictedAmpleLift E n H k d ha) (unrestrictedAmpleLabel E n j) := by
  rw [unrestrictedAmpleLiftSubgroupIso_curve]
  change p ≫ (d.curve.hom.group ≫ _) = _
  rw [← Category.assoc, hp]
  exact (unrestrictedLocusCurve E n).baseChangeCompEqIso_groupSection
    (unrestrictedAmpleOpen E n).ι (unrestrictedAmpleLift E n H k d ha) k
    (unrestrictedAmpleLift_inclusion E n H k d ha).symm _

/-- The prescribed original subgroup generator survives the ample lift itself. -/
theorem unrestrictedAmpleLiftSubgroupIso_generator (P : 𝟙_ (Over T) ⟶ H.carrier)
    (hP : P ≫ d.subgroup.hom = pullSection k (unrestrictedLocusGenerator E n)) :
    P ≫ (unrestrictedAmpleLiftSubgroupIso E n H k d ha).subgroup.hom =
      pullSection (unrestrictedAmpleLift E n H k d ha) (unrestrictedAmpleGenerator E n) := by
  change P ≫ (d.subgroup.hom ≫ _) = _
  rw [← Category.assoc, hP]
  exact (unrestrictedLocusSubgroup E n).compatibleBaseChangeCompEq_section
    (unrestrictedAmpleOpen E n).ι (unrestrictedAmpleLift E n H k d ha) k
    (unrestrictedAmpleLift_inclusion E n H k d ha).symm _

end FLT.Mazur.CyclicBoundaryParameter
