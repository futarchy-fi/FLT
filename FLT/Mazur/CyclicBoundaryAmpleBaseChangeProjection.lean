/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeModuli
public import FLT.Mazur.CompatibleSubgroupPullbackCast

/-!
# Original full curve projections under ample base change

The actual compatible subgroup comparison retains both stages of the original
whole-curve projection, including after restriction to the ample parameter open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleProjection_separated : IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance ampleProjection_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

local notation "F" => GeneralizedEllipticCurve.baseChange E g
local notation "q" => faithfulBaseChangeToOriginal g E.group n
local notation "I" => ampleParameterOpen (F) n
local notation "J" => ampleParameterOpen E n
local notation "A" => faithfulUniversalCurve (F) n
local notation "B" => faithfulUniversalCurve E n

/-- The ample comparison is the exact full compatible pullback transport. -/
theorem ampleBaseChangeSubgroupIso_eq :
    ampleBaseChangeSubgroupIso g E n =
      (faithfulBaseChangeTestSubgroupIso g E n (I).ι).trans
        (compatibleBaseChangeCompEq (faithfulUniversalSubgroup E n) (J).ι
          (ampleBaseChangeToOriginal g E n) ((I).ι ≫ (q))
          (ampleBaseChangeToOriginal_inclusion g E n).symm) :=
  compatibleBaseChangeCompEq_cast _ _ _ _ _ _

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- Every test transport retains the given original whole-curve map. -/
@[reassoc] theorem faithfulBaseChangeTestSubgroupIso_curve_fst {T : Scheme}
    (u : T ⟶ (cyclicFaithfulParameter (F).group n).left) :
    (faithfulBaseChangeTestSubgroupIso g E n u).curve.hom.curve.left ≫
        pullback.fst (B).curve.hom (u ≫ (q)) ≫
          pullback.fst E.curve.hom (cyclicFaithfulParameter E.group n).hom =
      pullback.fst (A).curve.hom u ≫
        pullback.fst (F).curve.hom (cyclicFaithfulParameter (F).group n).hom ≫
          pullback.fst E.curve.hom g := by
  change ((baseChangeMap u (faithfulBaseChangeCurveIso g E n).hom).curve.left ≫
    (compatibleBaseChangeComp (faithfulUniversalSubgroup E n) (q) u).curve.inv.curve.left) ≫
      _ ≫ _ = _
  simp only [Category.assoc, compatibleBaseChangeComp_inv_curve_fst_assoc,
    baseChangeMap_fst_assoc, faithfulBaseChangeCurveIso_curve_fst]

/-- Restricting to the ample open retains the original whole-curve morphism exactly. -/
@[reassoc] theorem ampleBaseChangeSubgroupIso_curve_fst :
    (ampleBaseChangeSubgroupIso g E n).curve.hom.curve.left ≫
        pullback.fst ((B).baseChange (J).ι).curve.hom (ampleBaseChangeToOriginal g E n) ≫
          pullback.fst (B).curve.hom (J).ι ≫
            pullback.fst E.curve.hom (cyclicFaithfulParameter E.group n).hom =
      pullback.fst (A).curve.hom (I).ι ≫
        pullback.fst (F).curve.hom (cyclicFaithfulParameter (F).group n).hom ≫
          pullback.fst E.curve.hom g := by
  rw [ampleBaseChangeSubgroupIso_eq]
  change ((faithfulBaseChangeTestSubgroupIso g E n (I).ι).curve.hom.curve.left ≫
    (compatibleBaseChangeCompEq (faithfulUniversalSubgroup E n) (J).ι
      (ampleBaseChangeToOriginal g E n) ((I).ι ≫ (q)) _).curve.hom.curve.left) ≫ _ ≫ _ ≫ _ = _
  rw [Category.assoc, compatibleBaseChangeCompEq_curve_fst_assoc,
    faithfulBaseChangeTestSubgroupIso_curve_fst]

end FLT.Mazur.CyclicBoundaryParameter
