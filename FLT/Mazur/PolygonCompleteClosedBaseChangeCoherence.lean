/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedBaseChangeIso
public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Repeated closed-fiber comparisons retain the same actual subgroup data

Direct and iterated extension of the original closed-polygon comparison agree
as full compatible isomorphisms. This equality includes the subgroup maps,
not only the full DR curves or their modular classes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T U : Scheme} (k : T ⟶ Spec (.of K)) (l : U ⟶ T)
local notation "b" => completeClosedBase K
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h

/-- Direct and repeated closed-fiber comparisons agree on the full curve and actual subgroup. -/
theorem completeClosedBaseChangeSubgroupIso_comp :
    (completeClosedBaseChangeSubgroupIso K n h (l ≫ k) ((l ≫ k) ≫ b) rfl).trans
      (compatibleBaseChangeComp (J) k l) =
    (compatibleBaseChangeCompEq (H) (k ≫ b) l ((l ≫ k) ≫ b) (Category.assoc l k b)).trans
      ((completeClosedBaseChangeSubgroupIso K n h k (k ≫ b) rfl).baseChange l) :=
  compatibleBaseChangeExtension_comp (H) b (completeClosedSubgroupIso K n h) k l

end FLT.Mazur.PolygonInfinitesimalStages
