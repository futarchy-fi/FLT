/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalLocalMaps
public import FLT.Mazur.WeierstrassDividedOlderIndexedNodeCover
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeCompatibility

/-!
# Equality-cycle terminal maps agree on the original node intersection

Both descended conic restrictions come from the same complete terminal component.
The full arbitrary-constant intersection theorem supplies scheme-map compatibility.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "l" => laurentConicComponentConic D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "f" => olderIndexedNodeMap hπ data D s hs 0 (by omega) (by omega) hk
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => positiveEqualityCycleTerminalFirstDesc data D s hs hk hp F w
local notation "d₂" => positiveEqualityCycleTerminalSecondDesc data D s hs hk hp F w

/-- The actual terminal node maps agree on any common scheme in their indexed chart. -/
theorem positiveEqualityCycleTerminalDesc_indexed_compatible {V : Scheme.{u}}
    (a b : V ⟶ Spec (.of (MiddleNodeOpen c))) (h : a ≫ f 0 = b ≫ f 1) :
    a ≫ d₁ = b ≫ d₂ := by
  apply residueMiddleNodeMaps_compatible D (start + s) (by omega) hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) d₁ d₂
    (l ≫ (J).inv ≫ ProjectiveLine.endpointReversal K ≫ F ⟨s + 2, by omega⟩)
  · simpa only [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter,
      Category.assoc, WeierstrassCurve.map_a₁] using
      positiveEqualityCycleTerminalFirstDesc_conic data D s hs hk hp F w
  · simpa only [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter,
      Category.assoc, WeierstrassCurve.map_a₁] using
      positiveEqualityCycleTerminalSecondDesc_conic data D s hs hk hp F w
  · change a ≫ (_ ≫ (olderSuccessiveTensorAtlasIso hπ data K s hs 0 (by omega)).hom) =
      b ≫ (_ ≫ (olderSuccessiveTensorAtlasIso hπ data K s hs 0 (by omega)).hom) at h
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono (olderSuccessiveTensorAtlasIso hπ data K s hs 0 (by omega)).hom).mp h

end FLT.Mazur.WeierstrassDividedDepth
