/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENS(E).
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedExteriorIntersections

/-!
# The preceding exterior intersection at every retained stage

The full preceding horizontal boundary remains the exact intersection with
an older successive chart after arbitrarily many later modifications.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "tail" => (finiteStageRetained hπ data (j + 1) hj r hr ≫
  Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 1 + r) hr))

/-- The entire preceding exterior inside every later finite model. -/
def olderPrecedingExterior : (E).carrier ⟶ finiteModification hπ data (j + 1 + r) hr :=
  (E).retained hπ e ≫ tail

instance olderPrecedingExterior_isOpenImmersion :
    IsOpenImmersion (olderPrecedingExterior hπ data j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- The original preceding boundary still commutes through both retained inclusions. -/
@[reassoc] theorem olderPrecedingExterior_overlap :
    (E).attach ≫ olderPrecedingExterior hπ data j hj r hr =
      previousToX hπ d e ≫ olderSuccessiveChart hπ data j hj r hr := by
  change (E).attach ≫ (E).retained hπ e ≫ tail =
    previousToX hπ d e ≫ (E).newX hπ e ≫ tail
  exact pushout.condition_assoc (f := (E).attach) (g := previousToX hπ d e) tail

/-- Later modifications introduce no new intersections with the preceding exterior. -/
theorem olderPrecedingExterior_preimage :
    olderSuccessiveChart hπ data j hj r hr ⁻¹'
      Set.range (olderPrecedingExterior hπ data j hj r hr) =
        Set.range (previousToX hπ d e) := by
  change (tail ∘ (E).newX hπ e) ⁻¹' Set.range (tail ∘ (E).retained hπ e) = _
  rw [Set.range_comp, Set.preimage_comp,
    Set.preimage_image_eq _ (tail).isOpenEmbedding.injective]
  exact (E).newX_retained_preimage hπ e

/-- The entire original boundary is cartesian at every retained finite stage. -/
theorem olderPrecedingExterior_isPullback :
    IsPullback (E).attach (previousToX hπ d e)
      (olderPrecedingExterior hπ data j hj r hr)
      (olderSuccessiveChart hπ data j hj r hr) := by
  apply IsOpenImmersion.isPullback
  · exact (olderPrecedingExterior_overlap hπ data j hj r hr).symm
  · exact TopologicalSpace.Opens.ext (olderPrecedingExterior_preimage hπ data j hj r hr)

/-- The original boundary is the complete horizontal principal open of the successive chart. -/
theorem previousToX_range_horizontal :
    Set.range (previousToX hπ d e) = Set.range
      (WeierstrassSuccessiveX.horizontalOpenInclusion W (π ^ (start + j)) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e)) := by
  unfold previousToX
  change Set.range ((WeierstrassSuccessiveX.horizontalOpenInclusion _ _ _ _ _ _) ∘
    ((WeierstrassSuccessiveX.horizontalIso _ _ _ _ _ _).inv ∘
      (previousBoundaryIso hπ d e).inv)) = _
  exact ((WeierstrassSuccessiveX.horizontalIso _ _ _ _ _ _).inv.homeomorph.surjective.comp
    (previousBoundaryIso hπ d e).inv.homeomorph.surjective).range_comp _

end FLT.Mazur.WeierstrassDividedDepth
