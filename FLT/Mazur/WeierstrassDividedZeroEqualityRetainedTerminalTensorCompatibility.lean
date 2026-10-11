/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentParameterBranchCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalLocalMaps

/-!
# The retained terminal neighbor at arbitrary terminal conic constant

The earlier conic is split, whereas the terminal constant is unrestricted.
The actual horizontal parameter branches prove compatibility on the whole overlap.
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
  (D : SplitNodeDepth W π depth) (t : ℕ) (hs : (t + 2) + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + (t + 2) + 1) ≤ depth)
  (hp : 2 * (start + (t + 2) + 1) = depth)
local notation "s" => t + 2
local notation "j" => (Fin.mk t (by omega) : Fin (s - 1))
local notation "K" => ResidueField R
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K (t + 1) (by omega) 0 hs
local notation "gNext" => olderGlobalTensorChart hπ data K (t + 2) hs 0 hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * (t + 2) + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "e" => data (Fin.mk (t + 2) (by omega))

/-- The penultimate tensor descent with its original source type exposed. -/
def zeroEqualityCyclePenultimateTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + (t + 1))) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  zeroEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp (by omega) j F w
local notation "d" => zeroEqualityCyclePenultimateTensorDesc hπ data D t hs hstart hk hp F w
local notation "dNext" => zeroEqualityCycleTerminalTensorDesc hπ data D s hs hk hp (by omega) F w

/-- The preceding and terminal retained charts agree on their entire intersection. -/
theorem zeroEqualityCycleRetainedTerminalTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentRetained_compatible_of_parameter_branch_restrictions hπ data D (t + 1)
    (by omega) (by omega) hs 0 hs (by omega) d dNext (by omega) hk
    (F ⟨s, by omega⟩) (F ⟨s + 2, by omega⟩)
  · rw [zeroEqualityCyclePenultimateTensorDesc,
      zeroEqualityCycleInteriorTensorDesc_first hπ data D s hs hstart hk hp (by omega) j F w]
    exact zeroEqualityCycleInteriorFirstLocalDesc_conic data D s hs hstart hk j F w
  · rw [zeroEqualityCyclePenultimateTensorDesc,
      zeroEqualityCycleInteriorTensorDesc_second hπ data D s hs hstart hk hp (by omega) j F w]
    have H := zeroEqualityCycleInteriorSecondLocalDesc_conic data D s hs hstart hk j F w
    have he : (⟨2 * s + 1 - (t + 1), by omega⟩ : Fin (2 * s + 2)) =
        ⟨s + 2, by omega⟩ := Fin.ext (by dsimp; omega)
    simpa only [Fin.val_mk, he] using H
  · rw [zeroEqualityCycleTerminalTensorDesc_first]
    exact zeroEqualityCycleTerminalFirstDesc_line data D s hs hk hp F w
  · rw [zeroEqualityCycleTerminalTensorDesc_second]
    exact zeroEqualityCycleTerminalSecondDesc_line data D s hs hk hp F w (by omega)

end FLT.Mazur.WeierstrassDividedDepth
