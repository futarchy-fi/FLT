/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedLineCharts
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLineBranches
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps

/-!
# Terminal positive-start descent recovers both complete original nodes

For the actual cyclic component family, both chosen descents are exactly
the complete original terminal inclusions, including the four-component cycle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "G₁" => olderGlobalResidueFirstNode hπ data D s hs 0 hs (by omega) hk
local notation "G₂" => olderGlobalResidueSecondNode hπ data D s hs 0 hs (by omega) hk
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveEqualityCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp
local notation "t" => WeierstrassDilatation.residueTangentUnit D

/-- Reversing the actual cyclic terminal component recovers its original parameterization. -/
@[reassoc] theorem positiveEqualityCycleComponent_terminal_unreverse :
    ProjectiveLine.endpointReversal K ≫ (Z ⟨s + 2, by omega⟩).left =
      laurentTerminalProjectiveComponent hπ data D s hs hk hp := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_terminal hπ data D s hs hstart hk hp)
  erw [H]
  change (ProjectiveLine.endpointReversalIso K).inv ≫
    (ProjectiveLine.endpointReversalIso K).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- The actual cyclic family recovers the complete first terminal attachment. -/
theorem positiveEqualityCycleTerminalFirstDesc_original :
    positiveEqualityCycleTerminalFirstDesc data D s hs hk hp F w = G₁ := by
  apply middleParameter_hom_ext c
  · rw [positiveEqualityCycleTerminalFirstDesc_conic,
      positiveEqualityCycleComponent_terminal_unreverse,
      equalityTerminalFirstNodeParameter_branch hπ data D s hs hk hp (by omega)]
  · apply middleNode_cancel_chartScaling (t)⁻¹
    rw [positiveEqualityCycleTerminalFirstDesc_line,
      positiveEqualityCycleComponent_retained_first_line_chart
        hπ data D s hs hstart hk hp s (by omega)]
    rw [olderGlobalResidueFirstNode_zero_transport
      hπ data D s (s - s) hs _ _ _ (Nat.sub_self s)]

/-- The opposite terminal map recovers the original node with its unchanged parameter. -/
theorem positiveEqualityCycleTerminalSecondDesc_original :
    positiveEqualityCycleTerminalSecondDesc data D s hs hk hp F w = G₂ := by
  apply middleParameter_hom_ext c
  · rw [positiveEqualityCycleTerminalSecondDesc_conic,
      positiveEqualityCycleComponent_terminal_unreverse,
      equalityTerminalSecondNodeParameter_branch hπ data D s hs hk hp (by omega)]
  · apply middleNode_cancel_chartScaling (-t)⁻¹
    rw [positiveEqualityCycleTerminalSecondDesc_line]
    have hi : s + 3 = 2 * s + 3 - s := by omega
    have he : (⟨s + 3, by omega⟩ : Fin (2 * s + 4)) =
        ⟨2 * s + 3 - s, by omega⟩ := Fin.ext hi
    rw [he, positiveEqualityCycleComponent_retained_second_line_chart
        hπ data D s hs hstart hk hp s (by omega)]
    rw [olderGlobalResidueSecondNode_zero_transport
      hπ data D s (s - s) hs _ _ _ (Nat.sub_self s)]

end FLT.Mazur.WeierstrassDividedDepth
