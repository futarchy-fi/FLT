/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoordinateSections
public import FLT.Mazur.PolygonArithmeticCompleteBaseSquare

/-!
# Constructed coordinates on the original resolved arithmetic thickenings

Base change of the specified resolved model to R/(π^(m+1)) constructs its
coordinate line and three sections at every order. The normalized equations
retain the original coefficients, with no choice of a different cubic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassDividedDepth
open FCurve WeierstrassIntegralChart PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The actual original resolved model over the m-th arithmetic coefficient quotient. -/
def finiteGlobalArithmeticStage (m : ℕ) : Scheme :=
  Limits.pullback (finiteGlobalStructure hπ data j hj) (baseToIntegral R π m)

/-- The original stage's projection to the same integral resolved model. -/
def finiteGlobalArithmeticProjection (m : ℕ) :
    finiteGlobalArithmeticStage hπ data j hj m ⟶ finiteGlobalModel hπ data j hj :=
  Limits.pullback.fst _ _

/-- The original arithmetic coefficient morphism at each order. -/
def finiteGlobalArithmeticStructure (m : ℕ) :
    finiteGlobalArithmeticStage hπ data j hj m ⟶ Spec (.of (Quotient R π m)) :=
  Limits.pullback.snd _ _

/-- The stage's actual contraction to the specified original cubic. -/
def finiteGlobalArithmeticToCubic (m : ℕ) :
    finiteGlobalArithmeticStage hπ data j hj m ⟶ integralCurve W :=
  finiteGlobalArithmeticProjection hπ data j hj m ≫ finiteGlobalContraction hπ data j hj

/-- The contraction retains exactly the original integral coefficients. -/
@[reassoc] theorem finiteGlobalArithmeticToCubic_toBase (m : ℕ) :
    finiteGlobalArithmeticToCubic hπ data j hj m ≫ integralCurveStructure W =
      finiteGlobalArithmeticStructure hπ data j hj m ≫ baseToIntegral R π m := by
  rw [finiteGlobalArithmeticToCubic, Category.assoc]
  exact Limits.pullback.condition

/-- The coordinate line on each actual resolved arithmetic thickening. -/
def finiteGlobalArithmeticCoordinateLine (m : ℕ) :
    (finiteGlobalArithmeticStage hπ data j hj m).Modules :=
  (Scheme.Modules.pullback (finiteGlobalArithmeticToCubic hπ data j hj m)).obj
    (integralCoordinateLine W)

/-- The three original coordinates constructed at every arithmetic order. -/
def finiteGlobalArithmeticCoordinateSection (m : ℕ) (i : Fin 3) :
    Γ(finiteGlobalArithmeticCoordinateLine hπ data j hj m, ⊤) :=
  pullGlobal (finiteGlobalArithmeticToCubic hπ data j hj m) (integralCoordinateLine W)
    (integralCoordinateSection W i)

/-- The line remains locally free over nonreduced arithmetic thickenings. -/
theorem finiteGlobalArithmeticCoordinateLine_locallyFreeRankOne (m : ℕ) :
    LocallyFreeRankOne (finiteGlobalArithmeticCoordinateLine hπ data j hj m) :=
  (integralCoordinateLine_locallyFreeRankOne W).pullback _

/-- The original three coordinates generate at every arithmetic order. -/
theorem finiteGlobalArithmeticCoordinateSections_cover (m : ℕ) :
    (⨆ i, sectionGeneratorOpen (finiteGlobalArithmeticCoordinateLine hπ data j hj m)
      (finiteGlobalArithmeticCoordinateSection hπ data j hj m i)) = ⊤ :=
  sectionGeneratorCover_pullback _ _ (integralCoordinateLine_locallyFreeRankOne W) 2
    (integralCoordinateSection W) (integralCoordinateSections_cover W)

/-- The constructed arithmetic coordinates satisfy the original normalized cubic equations. -/
theorem finiteGlobalArithmeticCoordinateSections_equations (m : ℕ) :
    CubicCoordinateEquations (finiteGlobalArithmeticCoordinateLine hπ data j hj m) W
      (finiteGlobalArithmeticCoordinateSection hπ data j hj m)
      ((finiteGlobalArithmeticStructure hπ data j hj m ≫ baseToIntegral R π m).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  rw [← finiteGlobalArithmeticToCubic_toBase]
  exact integralCoordinateSections_pullback_equations W _

end FLT.Mazur.WeierstrassDividedDepth
