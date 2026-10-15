/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedCover
public import FLT.Mazur.EllipticRetainedSmoothBoundaryCover
public import FLT.Mazur.SchemeSmoothChartTransport

/-!
# The positive-depth exterior cover at the actual final stage

Transport the original exterior and conic maps to the final resolved fiber.
The arithmetic boundary and conic open cover exactly its smooth restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "t" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)
local notation "g" => olderGlobalTensorChart hπ data F j (by omega) t (by omega)
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j
  (by omega) t (by omega) F
local notation "c" => olderGlobalConicBoundary hπ data D j (by omega) t
  (by omega) (by omega) (by omega)
local notation "p" => resolvedSplitStructure A D

/-- The whole retained exterior, preserving its original final-stage target. -/
def resolvedRetainedExteriorChart := g ≫ (E).hom

instance resolvedRetainedExteriorChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedExteriorChart A D j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The complete conic boundary with its original map transported to the final stage. -/
def resolvedRetainedConicChart := c ≫ (E).hom

instance resolvedRetainedConicChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedConicChart A D j hj0 hj) :=
  by
    unfold resolvedRetainedConicChart
    rw [← olderGlobalConicBoundary_transition]
    infer_instance

/-- At the final stage the two original boundaries cover exactly the smooth exterior. -/
theorem resolvedRetainedExterior_smooth_boundary_cover :
    Set.range (resolvedRetainedBoundaryChart A D j hj) ∪
      Set.range (resolvedRetainedConicChart A D j hj0 hj) =
    Set.range (resolvedRetainedExteriorChart A D j hj) ∩ (p).smoothLocus.carrier := by
  exact SchemeSmoothChartTransport.cover b c g E _ p
    (finiteTensorIndexIso_structure A hπ data F
      (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega))
    (retainedExterior_smooth_boundary_cover A hπ data D j
      (by omega) t (by omega) (by omega) (by omega))

end FLT.Mazur.WeierstrassDividedDepth
