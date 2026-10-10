/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalNodeIncidence
public import FLT.Mazur.WeierstrassDividedTerminalCrossedIntersection
public import FLT.Mazur.WeierstrassDividedTerminalZeroCrossedIntersection
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension
public import FLT.Mazur.SchemeDisjointBaseChange

/-!
# Terminal node and crossed component exclusions after coefficient extension

The actual global extension preserves the full empty intersections, at
positive preceding depth and depth zero, over any coefficient algebra.
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

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "ext" => globalResidueExtensionMap hπ data S (j + 1) hj
local notation "N" => terminalConicNodeSection hπ data D j hj hk hp
local notation "B₁" => terminalConicFirstBranch hπ data D j hj hk hp
local notation "B₂" => terminalConicSecondBranch hπ data D j hj hk hp
open WeierstrassSuccessiveX

section Positive
variable (hk0 : 0 < start + j)
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "A₁" => terminalConicFirstParameter hπ data D j hj hk0 hk
local notation "A₂" => terminalConicSecondParameter hπ data D j hj hk0 hk

/-- The full crossed first-parameter intersection stays empty over new coefficients. -/
theorem terminalPositiveExtendedFirst_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₁) (pullback.fst ext B₁) :=
  SchemeDisjointBaseChange.isPullback
    (terminalConicFirstParameter_cross_disjoint hπ data D j hj hk0 hk hp) ext

/-- The full crossed second-parameter intersection stays empty over new coefficients. -/
theorem terminalPositiveExtendedSecond_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₂) (pullback.fst ext B₂) :=
  SchemeDisjointBaseChange.isPullback
    (terminalConicSecondParameter_cross_disjoint hπ data D j hj hk0 hk hp) ext

/-- The actual terminal node misses the entire extended retained conic. -/
theorem terminalPositiveExtendedNode_conic_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext N) (pullback.fst ext (C ≫ g)) :=
  SchemeDisjointBaseChange.isPullback
    (terminalConicNodeSection_conic_disjoint hπ data D j hj hk hp hk0) ext

end Positive

section Zero
variable (hk0 : start + j = 0)
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "A₁" => terminalZeroConicFirstParameter hπ data D j hj hk0 hk
local notation "A₂" => terminalZeroConicSecondParameter hπ data D j hj hk0 hk

/-- The full crossed first-parameter intersection stays empty over new coefficients. -/
theorem terminalZeroExtendedFirst_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₁) (pullback.fst ext B₁) :=
  SchemeDisjointBaseChange.isPullback
    (terminalZeroConicFirstParameter_cross_disjoint hπ data D j hj hk0 hk hp) ext

/-- The full crossed second-parameter intersection stays empty over new coefficients. -/
theorem terminalZeroExtendedSecond_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₂) (pullback.fst ext B₂) :=
  SchemeDisjointBaseChange.isPullback
    (terminalZeroConicSecondParameter_cross_disjoint hπ data D j hj hk0 hk hp) ext

/-- The actual terminal node misses the entire extended retained conic. -/
theorem terminalZeroExtendedNode_conic_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext N) (pullback.fst ext (C ≫ g)) :=
  SchemeDisjointBaseChange.isPullback
    (terminalConicNodeSection_zeroConic_disjoint hπ data D j hj hk hp hk0) ext

end Zero

end FLT.Mazur.WeierstrassDividedDepth
