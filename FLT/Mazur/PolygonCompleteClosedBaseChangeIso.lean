/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedGeneratorIso
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# The original closed polygon after arbitrary further base change

The complete family pulled directly to a closed-fiber test scheme agrees with
the original closed polygon pulled to that same scheme, including its actual
finite subgroup and Cartier generator.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (k : T ⟶ Spec (.of K))
  (f : T ⟶ Spec (.of (PowerSeries K))) (w : f = k ≫ completeClosedBase K)
local notation "b" => completeClosedBase K
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "P" => completeOriginalGenerator K n h
local notation "Q" => completeClosedGenerator K n h
local notation "c" => completeClosedSubgroupIso K n h

/-- The actual original closed subgroup comparison survives every further base change. -/
def completeClosedBaseChangeSubgroupIso : CompatibleIso ((H).baseChange f) ((J).baseChange k) :=
  (compatibleBaseChangeCompEq (H) b k f w).trans ((c).baseChange k)

/-- The retained subgroup comparison uses the full closed DR comparison. -/
theorem completeClosedBaseChangeSubgroupIso_curve :
    (completeClosedBaseChangeSubgroupIso K n h k f w).curve =
      (completeGeneralizedCurve K n h).baseChangeCompEqIso b k f w ≪≫
        (baseChangeFunctor k).mapIso (completeClosedCurveIso K n h).symm := by
  change (compatibleBaseChangeCompEq (H) b k f w).curve ≪≫
    (baseChangeFunctor k).mapIso (c).curve = _
  rw [compatibleBaseChangeCompEq_curve, completeClosedSubgroupIso_curve]

/-- The comparison retains the actual pulled-back closed generator. -/
theorem completeClosedBaseChangeSubgroupIso_generator :
    pullSection f (P) ≫ (completeClosedBaseChangeSubgroupIso K n h k f w).subgroup.hom =
      pullSection k (Q) := by
  change pullSection f (P) ≫ ((compatibleBaseChangeCompEq (H) b k f w).subgroup.hom ≫
    (Over.pullback k).map (c).subgroup.hom) = _
  rw [← Category.assoc, compatibleBaseChangeCompEq_section, ← section_comp,
    completeClosedSubgroupIso_generator]

/-- Every original closed generator power is retained over every closed-fiber test scheme. -/
theorem completeClosedBaseChangeSubgroupIso_generator_pow (m : ℕ) :
    pullSection f ((P) ^ m) ≫
      (completeClosedBaseChangeSubgroupIso K n h k f w).subgroup.hom =
        pullSection k ((Q) ^ m) := by
  rw [section_pow, MonObj.pow_comp, completeClosedBaseChangeSubgroupIso_generator,
    section_pow]

end FLT.Mazur.PolygonInfinitesimalStages
