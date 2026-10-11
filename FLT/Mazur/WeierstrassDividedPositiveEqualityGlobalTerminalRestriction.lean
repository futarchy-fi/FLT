/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedEqualityTerminalParametersHomExt
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalBranches
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalBranches

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w

local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp

local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map
  (CommRingCat.ofHom (RingEquiv.toRingHom
    (AlgEquiv.toRingEquiv (WeierstrassModificationX.conicParameterNeg c))))

/-- The full first conic parameter recovers the reversed terminal family member. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_first_parameter :
    q₁ ≫ ρ ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      q₁ ≫ ρ ≫ F ⟨s + 2, by omega⟩ := by
  rw [positiveEqualityCycleComponent_terminal_first_parameter_assoc hπ data D s hs hstart
    hk hp, positiveEqualityCycleGlobalDesc_terminal_first,
    positiveEqualityCycleTerminalFirstDesc_conic]

/-- The opposite conic restriction keeps its original negative parameter. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_second_parameter :
    ν ≫ q₂ ≫ ρ ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      ν ≫ q₂ ≫ ρ ≫ F ⟨s + 2, by omega⟩ := by
  rw [positiveEqualityCycleComponent_terminal_second_parameter_assoc hπ data D s hs hstart
    hk hp, positiveEqualityCycleGlobalDesc_terminal_second,
    positiveEqualityCycleTerminalSecondDesc_conic]

/-- The original full Laurent chart recovers the reversed terminal family map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ (Z ⟨s + 2, by omega⟩).left ≫ d =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 2, by omega⟩ := by
  rw [positiveEqualityCycleComponent_terminal_chart_assoc]
  rw [← terminalLaurentAtlasIso_map_assoc hπ data D (s + 1) hs (by omega) hk hp,
    positiveEqualityCycleGlobalDesc_atlas, positiveEqualityCycleAtlasFamily_terminal,
    positiveEqualityCycleTerminalAtlasDesc_torus]

/-- The complete terminal component, including the Laurent chart, recovers its family map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_terminal_component :
    (Z ⟨s + 2, by omega⟩).left ≫ d = F ⟨s + 2, by omega⟩ := by
  apply (cancel_epi (ProjectiveLine.endpointReversalIso K).hom).mp
  apply equalityTerminalParameters_hom_ext data D s hs hk hp
  · exact positiveEqualityCycleGlobalDesc_terminal_first_parameter
      hπ data D s hs hstart hk hp F w
  · let _ : IsIso ν := by
      change IsIso (Scheme.Spec.mapIso
        (WeierstrassModificationX.conicParameterNeg c).toRingEquiv.toCommRingCatIso.op).hom
      infer_instance
    apply (cancel_epi ν).mp
    exact positiveEqualityCycleGlobalDesc_terminal_second_parameter
      hπ data D s hs hstart hk hp F w
  · exact positiveEqualityCycleGlobalDesc_terminal_torus
      hπ data D s hs hstart hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
