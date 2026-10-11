/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc
public import FLT.Mazur.WeierstrassDividedEqualityTerminalParametersHomExt
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoBranches
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoBranches
import all FLT.Mazur.WeierstrassDividedZeroEqualityCycleEndCharts
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoAtlas
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc

/-!
# Global descent on the complete reversed equality-depth terminal component

The full conic parameter opens and Laurent chart recover the prescribed map.
Both conic parameters keep their original tangent signs and localizations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityLengthTwoGlobalDesc hπ data D hs hstart hk hp F w

local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp

local notation "e" => data (Fin.mk (0 + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D 0 hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D 0 hs hk hp
local notation "ρ" => Iso.inv (ProjectiveLine.endpointReversalIso K)
/-- The full first conic parameter recovers the reversed terminal family member. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_terminal_first_parameter :
    q₁ ≫ ρ ≫ (Z 1).left ≫ d =
      q₁ ≫ ρ ≫ F 1 := by
  rw [zeroEqualityCycleComponent_lengthTwo_first_conic_assoc hπ data D hs hstart
    hk hp, zeroEqualityLengthTwoGlobalDesc_first,
    zeroEqualityLengthTwoFirstDesc_conic]
  rfl

/-- The opposite conic restriction keeps its original negative parameter. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_terminal_second_parameter :
    q₂ ≫ ρ ≫ (Z 1).left ≫ d =
      q₂ ≫ ρ ≫ F 1 := by
  rw [zeroEqualityCycleComponent_lengthTwo_second_conic_assoc hπ data D hs hstart
    hk hp, zeroEqualityLengthTwoGlobalDesc_second,
    zeroEqualityLengthTwoSecondDesc_conic]
  rfl

/-- The original full Laurent chart recovers the reversed terminal family map. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_terminal_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ (Z 1).left ≫ d =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ F 1 := by
  rw [show (1 : Fin (2 * 0 + 2)) = ⟨0 + 1, by omega⟩ from rfl,
    zeroEqualityCycleComponent_terminal_chart_assoc]
  rw [← terminalLaurentAtlasIso_map_assoc hπ data D (0 + 1) hs (by omega) hk hp,
    zeroEqualityLengthTwoGlobalDesc_atlas]
  change _ ≫ zeroEqualityCycleTerminalAtlasDesc hπ data D 0 hs hk hp F = _
  rw [zeroEqualityCycleTerminalAtlasDesc_torus]

/-- The complete terminal component, including the Laurent chart, recovers its family map. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_terminal_component :
    (Z 1).left ≫ d = F 1 := by
  apply (cancel_epi (ProjectiveLine.endpointReversalIso K).hom).mp
  apply equalityTerminalParameters_hom_ext data D 0 hs hk hp
  · exact zeroEqualityLengthTwoGlobalDesc_terminal_first_parameter
      hπ data D hs hstart hk hp F w
  · exact zeroEqualityLengthTwoGlobalDesc_terminal_second_parameter
      hπ data D hs hstart hk hp F w
  · exact zeroEqualityLengthTwoGlobalDesc_terminal_torus
      hπ data D hs hstart hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
