/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialConicContraction
public import FLT.Mazur.WeierstrassDividedInitialComponentStructure
public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Both complete initial exceptional components contract to the original node

The complete maps retain their original conic charts and reciprocal gluing.
Separatedness extends the actual conic contraction equality across infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data (1 + r) hr
local notation "c" => finiteGlobalContraction hπ data (1 + r) hr
local notation "ν" => initialOriginalCubicNode data D hstart
local notation "f₁" => initialGlobalFirstComponent hπ data D h1 hstart hk r hr
local notation "f₂" => initialGlobalSecondComponent hπ data D h1 hstart hk r hr

/-- The whole first exceptional component has its original constant cubic projection. -/
@[reassoc] theorem initialGlobalFirstComponent_contraction :
    f₁ ≫ pullback.snd q g ≫ c = toBase K ≫ ν := by
  refine ext_of_isDominant_of_isSeparated (integralCurveStructure W) ?_ (left K) ?_
  · rw [Category.assoc, Category.assoc, ← finiteGlobalStructure,
      ← pullback.condition, ← Category.assoc, initialGlobalFirstComponent_structure,
      Category.assoc, initialOriginalCubicNode_base]
  · rw [initialGlobalFirstComponent_left_assoc,
      initialGlobalConicFirstParameter_contraction, conicZeroAffineIso_structure_assoc,
      left_toBase_assoc]

/-- The whole opposite exceptional component contracts to that same original node. -/
@[reassoc] theorem initialGlobalSecondComponent_contraction :
    f₂ ≫ pullback.snd q g ≫ c = toBase K ≫ ν := by
  refine ext_of_isDominant_of_isSeparated (integralCurveStructure W) ?_ (left K) ?_
  · rw [Category.assoc, Category.assoc, ← finiteGlobalStructure,
      ← pullback.condition, ← Category.assoc, initialGlobalSecondComponent_structure,
      Category.assoc, initialOriginalCubicNode_base]
  · rw [initialGlobalSecondComponent_left_assoc,
      initialGlobalConicSecondParameter_contraction, conicZeroAffineIso_structure_assoc,
      left_toBase_assoc]

/-- The two complete original exceptional components have the same cubic projection. -/
theorem initialExceptionalComponents_same_contraction :
    f₁ ≫ pullback.snd q g ≫ c = f₂ ≫ pullback.snd q g ≫ c := by
  rw [initialGlobalFirstComponent_contraction, initialGlobalSecondComponent_contraction]

end FLT.Mazur.WeierstrassDividedDepth
