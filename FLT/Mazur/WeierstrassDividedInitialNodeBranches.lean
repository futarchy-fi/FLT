/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialIncidenceLine
public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceBranch

/-!
# Complete branches of the original initial nodes

Both full node inclusions retain the original conic parameters and incidence
line, including the slope translation on the second tangent chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "G" => initialGlobalResidueFiberChart hπ data D j hj hstart hk

/-- The first original node retains its entire conic parameter. -/
@[reassoc] theorem initialGlobalFirstNode_conicBranch :
    (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
        initialGlobalResidueFirstNode hπ data D j hj hstart hk =
      initialGlobalConicFirstParameter hπ data D j hj hstart hk := by
  change _ ≫ _ ≫ fullFirstNodeChart a c ha ≫ G = _
  rw [fullNodeFirstBranch_firstChart_assoc]
  rfl

/-- The second original node retains its entire opposite conic parameter. -/
@[reassoc] theorem initialGlobalSecondNode_conicBranch :
    (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫ fullNodeFirstBranch (-a) c (ha).neg ≫
        initialGlobalResidueSecondNode hπ data D j hj hstart hk =
      initialGlobalConicSecondParameter hπ data D j hj hstart hk := by
  change _ ≫ _ ≫ fullSecondNodeChart a c ha ≫ G = _
  rw [fullNodeFirstBranch_secondChart_assoc]
  rfl

/-- The first incidence branch is the original localized incidence line. -/
@[reassoc] theorem initialGlobalFirstNode_incidenceBranch :
    fullNodeSecondBranch a c ha ≫ initialGlobalResidueFirstNode hπ data D j hj hstart hk =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
          initialGlobalIncidenceLine hπ data D j hj hstart hk := by
  change _ ≫ fullFirstNodeChart a c ha ≫ G = _
  rw [fullNodeSecondBranch_firstChart_assoc]
  rfl

/-- The second incidence branch keeps its original translated slope. -/
@[reassoc] theorem initialGlobalSecondNode_incidenceBranch :
    fullNodeSecondBranch (-a) c (ha).neg ≫
        initialGlobalResidueSecondNode hπ data D j hj hstart hk =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
      Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        initialGlobalIncidenceLine hπ data D j hj hstart hk := by
  change _ ≫ fullSecondNodeChart a c ha ≫ G = _
  rw [fullNodeSecondBranch_secondChart_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
