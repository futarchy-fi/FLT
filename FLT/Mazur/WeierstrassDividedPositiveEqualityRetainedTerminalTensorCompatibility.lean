/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
public import FLT.Mazur.WeierstrassDividedAdjacentParameterBranchCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps

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
  (D : SplitNodeDepth W π depth) (t : ℕ) (hs : (t + 1) + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + (t + 1) + 1) ≤ depth)
  (hp : 2 * (start + (t + 1) + 1) = depth)
local notation "s" => t + 1
local notation "j" => (Fin.mk t (by omega) : Fin s)
local notation "K" => ResidueField R
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K t (by omega) 0 hs
local notation "gNext" => olderGlobalTensorChart hπ data K (t + 1) hs 0 hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * (t + 1) + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "e" => data (Fin.mk (t + 1) (by omega))

/-- The penultimate tensor descent with its original source type exposed. -/
def positiveEqualityCyclePenultimateTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + t)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  positiveEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp j F w
local notation "d" => positiveEqualityCyclePenultimateTensorDesc hπ data D t hs hstart hk hp F w
local notation "dNext" => positiveEqualityCycleTerminalTensorDesc hπ data D s hs hstart hk hp F w

/-- The preceding and terminal retained charts agree on their entire intersection. -/
theorem positiveEqualityCycleRetainedTerminalTensorDesc_compatible :
    Limits.pullback.fst g gNext ≫ d = Limits.pullback.snd g gNext ≫ dNext := by
  apply adjacentRetained_compatible_of_parameter_branch_restrictions hπ data D t
    (by omega) (by omega) hs 0 hs (by omega) d dNext (by omega) hk
    (F ⟨s + 1, by omega⟩) (F ⟨s + 3, by omega⟩)
  · rw [positiveEqualityCyclePenultimateTensorDesc,
      positiveEqualityCycleInteriorTensorDesc_first hπ data D s hs hstart hk hp j F w]
    exact positiveEqualityCycleInteriorFirstLocalDesc_conic data D s hs hk j F w
  · rw [positiveEqualityCyclePenultimateTensorDesc,
      positiveEqualityCycleInteriorTensorDesc_second hπ data D s hs hstart hk hp j F w]
    have H := positiveEqualityCycleInteriorSecondLocalDesc_conic data D s hs hk j F w
    have he : (⟨2 * s + 2 - t, by omega⟩ : Fin (2 * s + 4)) =
        ⟨s + 3, by omega⟩ := Fin.ext (by dsimp; omega)
    simpa only [Fin.val_mk, he] using H
  · rw [positiveEqualityCycleTerminalTensorDesc_first]
    exact positiveEqualityCycleTerminalFirstDesc_line data D s hs hk hp F w
  · rw [positiveEqualityCycleTerminalTensorDesc_second]
    exact positiveEqualityCycleTerminalSecondDesc_line data D s hs hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
