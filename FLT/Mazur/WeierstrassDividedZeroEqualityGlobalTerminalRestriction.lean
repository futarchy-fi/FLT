/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedEqualityTerminalParametersHomExt
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalBranches
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc

/-!
# Global descent on the complete reversed equality-depth terminal component

The full conic parameter opens and Laurent chart recover the prescribed map.
The second conic parameter keeps its sign before cancellation of its involution.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map
  (CommRingCat.ofHom (RingEquiv.toRingHom
    (AlgEquiv.toRingEquiv (WeierstrassModificationX.conicParameterNeg c))))

/-- The full first conic parameter recovers the reversed terminal family member. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_first_parameter :
    q₁ ≫ ρ ≫ (Z ⟨s + 1, by omega⟩).left ≫ d =
      q₁ ≫ ρ ≫ F ⟨s + 1, by omega⟩ := by
  rw [zeroEqualityCycleComponent_terminal_first_parameter_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_terminal_first,
    zeroEqualityCycleTerminalFirstDesc_conic]

/-- The opposite conic restriction keeps its original negative parameter. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_second_parameter :
    ν ≫ q₂ ≫ ρ ≫ (Z ⟨s + 1, by omega⟩).left ≫ d =
      ν ≫ q₂ ≫ ρ ≫ F ⟨s + 1, by omega⟩ := by
  rw [zeroEqualityCycleComponent_terminal_second_parameter_assoc hπ data D s hs hstart
    hk hp hpos, zeroEqualityPositiveCycleGlobalDesc_terminal_second,
    zeroEqualityCycleTerminalSecondDesc_conic]

/-- The original full Laurent chart recovers the reversed terminal family map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ (Z ⟨s + 1, by omega⟩).left ≫ d =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 1, by omega⟩ := by
  rw [zeroEqualityCycleComponent_terminal_chart_assoc]
  rw [← terminalLaurentAtlasIso_map_assoc hπ data D (s + 1) hs (by omega) hk hp,
    zeroEqualityPositiveCycleGlobalDesc_atlas, zeroEqualityPositiveCycleAtlasFamily_terminal,
    zeroEqualityCycleTerminalAtlasDesc_torus]

/-- The complete terminal component, including the Laurent chart, recovers its family map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_terminal_component :
    (Z ⟨s + 1, by omega⟩).left ≫ d = F ⟨s + 1, by omega⟩ := by
  apply (cancel_epi (ProjectiveLine.endpointReversalIso K).hom).mp
  apply equalityTerminalParameters_hom_ext data D s hs hk hp
  · exact zeroEqualityPositiveCycleGlobalDesc_terminal_first_parameter
      hπ data D s hs hstart hk hp hpos F w
  · let _ : IsIso ν := by
      change IsIso (Scheme.Spec.mapIso
        (WeierstrassModificationX.conicParameterNeg c).toRingEquiv.toCommRingCatIso.op).hom
      infer_instance
    apply (cancel_epi ν).mp
    exact zeroEqualityPositiveCycleGlobalDesc_terminal_second_parameter
      hπ data D s hs hstart hk hp hpos F w
  · exact zeroEqualityPositiveCycleGlobalDesc_terminal_torus
      hπ data D s hs hstart hk hp hpos F w

end FLT.Mazur.WeierstrassDividedDepth
