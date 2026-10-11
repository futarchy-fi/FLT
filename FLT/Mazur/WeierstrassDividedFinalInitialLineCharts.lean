/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalInitialComponents
public import FLT.Mazur.WeierstrassDividedOlderParameterNodeBranches

/-!
# Initial components retain both complete first horizontal branches

The signed reciprocal chart scalings are retained at the original first pair
of positive-depth nodes, with only the final model index transported.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "e" => data (Fin.mk 1 (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := 1 + s) (b := s + 1) (by omega) hs (by omega))

/-- The first initial component's second chart is the complete first retained line. -/
@[reassoc] theorem finalInitialComponent_first_right_parameterBranch :
    ProjectiveLine.right K ≫ finalInitialComponent hπ data D s hs hstart hk 0 =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleParameterLineBranch c ≫
        olderGlobalResidueFirstNode hπ data D 0 (by omega) s (by omega)
          hstart (by omega) ≫ transport := by
  change ProjectiveLine.right K ≫
    initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega) ≫
      transport = _
  rw [initialGlobalFirstComponent_right_assoc,
    olderGlobalResidueFirstNode_parameterLineBranch_assoc]

/-- The second initial component's second chart is the complete first retained line. -/
@[reassoc] theorem finalInitialComponent_second_right_parameterBranch :
    ProjectiveLine.right K ≫ finalInitialComponent hπ data D s hs hstart hk 1 =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleParameterLineBranch c ≫
        olderGlobalResidueSecondNode hπ data D 0 (by omega) s (by omega)
          hstart (by omega) ≫ transport := by
  change ProjectiveLine.right K ≫
    initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega) ≫
      transport = _
  rw [initialGlobalSecondComponent_right_assoc,
    olderGlobalResidueSecondNode_parameterLineBranch_assoc]

end FLT.Mazur.WeierstrassDividedDepth
