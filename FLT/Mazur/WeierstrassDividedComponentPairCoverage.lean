/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentComponentRanges
public import FLT.Mazur.WeierstrassDividedConicParameterTransport
public import FLT.Mazur.WeierstrassDividedTerminalComponentRanges
public import FLT.Mazur.WeierstrassDividedZeroExteriorCoverage

/-!
# Projective component pairs contain the complete original conics

Adjacent pairs give the preceding full conic and both next lines; terminal
pairs give their full conic and terminal chart. The exterior keeps infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
/-- Postcomposition carries an exact two-image cover to an exact two-image cover. -/
theorem componentRange_union_postcomp {A B C X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (h : C ⟶ X) (t : X ⟶ Y)
    (he : Set.range f ∪ Set.range g = Set.range h) :
    Set.range (f ≫ t) ∪ Set.range (g ≫ t) = Set.range (h ≫ t) := by
  change Set.range (t ∘ f) ∪ Set.range (t ∘ g) = Set.range (t ∘ h)
  simp only [Set.range_comp, ← Set.image_union, he]

/-- The terminal positive pair contains its whole conic and whole terminal chart. -/
theorem terminalComponents_conic_range (hp : 2 * (start + j + 1) < depth)
    (hk0 : 0 < start + j) :
    Set.range (terminalFirstComponent hπ data D j hj hk0 hk hp) ∪
        Set.range (terminalSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (olderGlobalMiddleConic hπ data D j hj 0 hj hk0 hk) ∪
        Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  rw [terminalComponents_range, terminalConicFirstParameter_retained,
    terminalConicSecondParameter_retained, olderGlobalMiddleConicParameters_cover]

/-- The terminal zero pair contains its whole conic and whole terminal chart. -/
theorem terminalZeroComponents_conic_range (hp : 2 * (start + j + 1) < depth)
    (hk0 : start + j = 0) :
    Set.range (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) ∪
        Set.range (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (olderGlobalZeroConic hπ data D j hj 0 hj hk0 hk) ∪
        Set.range (terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp) := by
  rw [terminalZeroComponents_range, terminalZeroConicFirstParameter_retained,
    terminalZeroConicSecondParameter_retained, olderGlobalZeroConicParameters_cover]

variable (r : ℕ) (hr : j + 2 + r ≤ n)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K
    (a := j + 1 + (r + 1)) (b := j + 2 + r) (by omega) hr (by omega))

/-- The adjacent retained pair gives the entire preceding conic and both next lines. -/
theorem adjacentRetainedComponents_conic_range (hk0 : 0 < start + j) :
    Set.range (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ∪
        Set.range (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (olderGlobalMiddleConic hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport) ∪
        (Set.range (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext)) := by
  rw [adjacentRetainedFirstComponent_range, adjacentRetainedSecondComponent_range,
    adjacentRetainedFirstParameter_transport, adjacentRetainedSecondParameter_transport]
  have H := componentRange_union_postcomp
    (olderGlobalMiddleConicFirstParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
    (olderGlobalMiddleConicSecondParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
    (olderGlobalMiddleConic hπ data D j hj (r + 1) (by omega) hk0 hk) transport
    (olderGlobalMiddleConicParameters_cover hπ data D j hj (r + 1) (by omega) hk0 hk)
  exact (Set.union_union_union_comm _ _ _ _).trans (congrArg (· ∪ _) H)

/-- The adjacent zero pair gives the entire preceding conic and both next lines. -/
theorem adjacentZeroComponents_conic_range (hk0 : start + j = 0) :
    Set.range (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ∪
        Set.range (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (olderGlobalZeroConic hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport) ∪
        (Set.range (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext)) := by
  rw [adjacentZeroFirstComponent_range, adjacentZeroSecondComponent_range,
    adjacentZeroFirstParameter_transport, adjacentZeroSecondParameter_transport]
  have H := componentRange_union_postcomp
    (olderGlobalZeroConicFirstParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
    (olderGlobalZeroConicSecondParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
    (olderGlobalZeroConic hπ data D j hj (r + 1) (by omega) hk0 hk) transport
    (olderGlobalZeroConicParameters_cover hπ data D j hj (r + 1) (by omega) hk0 hk)
  exact (Set.union_union_union_comm _ _ _ _).trans (congrArg (· ∪ _) H)

end FLT.Mazur.WeierstrassDividedDepth
