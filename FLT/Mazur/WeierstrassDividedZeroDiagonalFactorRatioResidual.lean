/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioBoundary
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonExterior
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioCover

/-!
# Exact residuals for the full diagonal factor-ratio gluing

The initial-to-retained square is equivalent to an explicit Laurent equation.
The transported infinity boundaries also retain their exact transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D
local notation "t" => PolygonArithmeticSimultaneous.State.last D
local notation "P" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "B" => arithmeticZeroDiagonalFactorRatioBoundaryIso hπ data H m hj u hu
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu
local notation "g" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "I" => arithmeticZeroDiagonalInitialInfinityBoundary hπ data H m hj u hu

/-- The full initial puncture has its exact, generally nonstandard retained-side parameter. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_retained_boundary (b : Bool) :
    P b ≫ f b =
      (B b).hom ≫ (edgeInversion Q).hom ≫ rightBranchOpen Q (t m b) ≫ g b := by
  rw [arithmeticZeroDiagonalFactorRatioInitialMap, ← Category.assoc,
    arithmeticZeroDiagonalInitialFactorRatio_puncture, Category.assoc,
    arithmeticZeroDiagonalPolygon_initial_retained]

/-- Agreement on the full original initial edge is exactly the stated Laurent equation. -/
theorem arithmeticZeroDiagonalFactorRatioInitialMap_retained_iff (b : Bool) :
    P b ≫ f b =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom ≫
        rightBranchOpen Q (t m b) ≫ g b ↔
      (B b).hom ≫ (edgeInversion Q).hom =
        (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom := by
  rw [arithmeticZeroDiagonalFactorRatioInitialMap_retained_boundary]
  rw [← Category.assoc (B b).hom (edgeInversion Q).hom]
  exact cancel_mono (rightBranchOpen Q (t m b) ≫ g b)

omit [IsBezout R] in
/-- The full infinity-side boundary keeps the accumulated right-puncture substitution. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialInfinityBoundary_parameter (b : Bool) :
    I b = (A b false).hom ≫ rightBranchOpen Q (s m b) ≫ C b := by
  unfold arithmeticZeroDiagonalInitialInfinityBoundary
  have h := arithmeticZeroDiagonalInitialTotalNodeIso_puncture hπ data H m hj u hu b false
  simpa only [punctureOpen_false, Category.assoc] using congrArg (· ≫ C b) h

/-- The exact transition between the two full transported infinity boundaries. -/
def arithmeticZeroDiagonalInfinityBoundaryTransition : branchTorus Q ≅ branchTorus Q :=
  A true false ≪≫ edgeInversion Q ≪≫ (A false false).symm

local notation "J" => arithmeticZeroDiagonalInfinityBoundaryTransition hπ data H m hj u hu

omit [IsBezout R] in
/-- Both original infinity-side boundaries agree after their full accumulated transition. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialInfinityBoundary_transition :
    I true = (J).hom ≫ I false := by
  rw [arithmeticZeroDiagonalInitialInfinityBoundary_parameter,
    arithmeticZeroDiagonalInitialInfinityBoundary_parameter,
    arithmeticZeroDiagonalPolygon_infinity]
  simp only [arithmeticZeroDiagonalInfinityBoundaryTransition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

omit [IsBezout R] in
/-- Both complete transported infinity boundaries have the same open image. -/
theorem arithmeticZeroDiagonalInitialInfinityBoundary_range : Set.range (I true) =
    Set.range (I false) := by
  rw [arithmeticZeroDiagonalInitialInfinityBoundary_transition]
  change Set.range (I false ∘ (J).hom) = _
  have h : Function.Surjective (J).hom := (J).hom.homeomorph.surjective
  rw [Set.range_comp, h.range_eq, Set.image_univ]

end FLT.Mazur.WeierstrassDividedDepth
