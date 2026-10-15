/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveSimpleSlopeChart
public import FLT.Mazur.WeierstrassSuccessiveNilpotentNodeChart
public import FLT.Mazur.QuadraticRootOppositeBranch

/-!
# The opposite original polygon node branch over a nilpotent base

The second branch is constructed from the original coefficients and the
already constructed small root. Both branch denominators are functions on
the original successive chart, and their principal opens partition it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "v" => nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "a" => nodeSlopeLinear W π b3
local notation "b" => nodeSlopeConstant W s π b4 b6

/-- The original slope on the opposite branch, with no extra Hensel choice. -/
def oppositeNodeSlope : SuccessiveIncidence.Coordinate π :=
  QuadraticRootBranchLocalization.oppositeRoot a v

/-- The opposite slope solves the same original equation. -/
theorem oppositeNodeSlope_equation :
    oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 ^ 2 +
      a * oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 = b :=
  QuadraticRootBranchLocalization.oppositeRoot_equation a b v
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite root is simple over the whole original node ring. -/
theorem oppositeNodeSlope_simple :
    IsUnit (oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 +
      oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 + a) :=
  QuadraticRootBranchLocalization.oppositeRoot_simple a v
    (nilpotentNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite polygon node open in the original successive equation. -/
def oppositePolygonChart : Spec (.of (PolygonSmoothing.ChartRing π)) ⟶
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  simpleSlopePolygonChart W s π b3 b4 b6
    (oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (oppositeNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite node open has a proved inverse on its entire principal branch. -/
theorem oppositePolygonChart_isOpenImmersion :
    IsOpenImmersion (oppositePolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) :=
  simpleSlopePolygonChart_isOpenImmersion W s π b3 b4 b6 _ _
    (oppositeNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite branch keeps the original coefficient map. -/
@[reassoc] theorem oppositePolygonChart_structure :
    oppositePolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s π b3 b4 b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing π))) :=
  simpleSlopePolygonChart_structure ..

/-- A branch denominator expressed in the original three-coordinate algebra. -/
def originalSlopeDenominator (r : SuccessiveIncidence.Coordinate π) :
    Coordinate W s π b3 b4 b6 :=
  fromMonic W s π b3 b4 b6 (QuadraticRootBranchLocalization.denominator a b r)

/-- The two original principal branch opens cover every point of the successive chart. -/
theorem originalSlopeBranches_cover (p : PrimeSpectrum (Coordinate W s π b3 b4 b6)) :
    originalSlopeDenominator W s π b3 b4 b6 v ∉ p.asIdeal ∨
      originalSlopeDenominator W s π b3 b4 b6
        (oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) ∉ p.asIdeal :=
  QuadraticRootBranchLocalization.branch_cover a b v
    (nilpotentNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (PrimeSpectrum.comap (fromMonic W s π b3 b4 b6).toRingHom p)

/-- The two original principal branch opens have empty intersection. -/
theorem originalSlopeBranches_disjoint (p : PrimeSpectrum (Coordinate W s π b3 b4 b6)) :
    ¬ (originalSlopeDenominator W s π b3 b4 b6 v ∉ p.asIdeal ∧
      originalSlopeDenominator W s π b3 b4 b6
        (oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) ∉ p.asIdeal) :=
  QuadraticRootBranchLocalization.branch_disjoint a b v
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (PrimeSpectrum.comap (fromMonic W s π b3 b4 b6).toRingHom p)

end FLT.Mazur.WeierstrassSuccessiveX
