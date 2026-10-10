/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalZeroConicIntersection
public import FLT.Mazur.WeierstrassDividedTerminalConicCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicOrigin
public import FLT.Mazur.PolygonCyclicCocone

/-!
# Terminal ordered branches and the node excluded from the retained conic

The original terminal normalization gives both affine branches and their shared
node section. The full retained conic misses that section, including at depth zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "G" => terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "o" => PolygonNodePresentation.aOrigin K

/-- The original terminal node as a section in the actual global model. -/
def terminalConicNodeSection := o ≫ G

/-- The complete ordered first affine branch in the actual terminal chart. -/
def terminalConicFirstBranch := PolygonCyclicAtlas.firstBranch K ≫ G

/-- The complete ordered second affine branch in the actual terminal chart. -/
def terminalConicSecondBranch := PolygonCyclicAtlas.secondBranch K ≫ G

/-- The origin on the first full branch is the original terminal node section. -/
@[reassoc] theorem terminalConicFirstBranch_origin :
    ProjectiveLine.chartZero K ≫ terminalConicFirstBranch hπ data D j hj hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [terminalConicFirstBranch, ← Category.assoc, PolygonCyclicAtlas.zero_firstBranch]
  rfl

/-- The origin on the second full branch is the same original terminal node section. -/
@[reassoc] theorem terminalConicSecondBranch_origin :
    ProjectiveLine.chartZero K ≫ terminalConicSecondBranch hπ data D j hj hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [terminalConicSecondBranch, ← Category.assoc, PolygonCyclicAtlas.zero_secondBranch]
  rfl

open WeierstrassSuccessiveX
section Positive
variable (hk0 : 0 < start + j)
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

/-- The terminal node is disjoint from the entire preceding positive-depth conic. -/
theorem terminalConicNodeSection_conic_disjoint :
    Disjoint (Set.range (terminalConicNodeSection hπ data D j hj hk hp))
      (Set.range (C ≫ g)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (terminalNodeConicCoordinates_isPullback hπ data D j hj hk0 hk hp) (o a) b hb.symm
  exact Set.disjoint_left.mp (residueNodeConicOrigin_disjoint D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d) hp) ⟨v, hv⟩ ⟨a, rfl⟩

/-- The terminal-node and full preceding conic intersection is the empty scheme. -/
theorem terminalConicNodeSection_conic_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (terminalConicNodeSection hπ data D j hj hk hp) (C ≫ g) := by
  let _ := Scheme.isEmpty_pullback _ _
    (terminalConicNodeSection_conic_disjoint hπ data D j hj hk hp hk0)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback _ _)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end Positive

section Zero
variable (hk0 : start + j = 0)
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

/-- The terminal node also misses the entire original scale-one conic. -/
theorem terminalConicNodeSection_zeroConic_disjoint :
    Disjoint (Set.range (terminalConicNodeSection hπ data D j hj hk hp))
      (Set.range (C ≫ g)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (terminalNodeZeroConicCoordinates_isPullback hπ data D j hj hk0 hk hp) (o a) b hb.symm
  exact Set.disjoint_left.mp (residueNodeConicOrigin_disjoint D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d) hp) ⟨v, hv⟩ ⟨a, rfl⟩

/-- The terminal-node and full scale-one conic fiber product is the empty scheme. -/
theorem terminalConicNodeSection_zeroConic_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (terminalConicNodeSection hπ data D j hj hk hp) (C ≫ g) := by
  let _ := Scheme.isEmpty_pullback _ _
    (terminalConicNodeSection_zeroConic_disjoint hπ data D j hj hk hp hk0)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback _ _)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end Zero

end FLT.Mazur.WeierstrassDividedDepth
