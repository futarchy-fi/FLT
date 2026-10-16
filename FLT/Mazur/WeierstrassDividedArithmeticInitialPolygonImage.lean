/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioChartImage
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioLabeledMaps

/-!
# Images of the original arithmetic initial labels

The exact original full node comparisons are open immersions. Their images
retain the deleted normalized tangent divisor at every arithmetic order,
and the missing points lie on the corresponding complete infinity edge.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "f" => arithmeticFactorRatioLabeledInitialMap data H hπ m k hk
local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3) (by omega)
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso Q τ)) (𝟙 (PolygonSmoothing.chart Q τ))

/-- The original initial labeled maps have exactly the normalized full-node formulas. -/
theorem arithmeticFactorRatioLabeledInitialMap_normalized (b : Bool) :
    f b = N ≫ O b ≫ c (initialPolygonIndex k b) :=
  arithmeticFactorRatioTensorAffineMap_chart ..

/-- Every original initial label is embedded, with all polynomial corrections retained. -/
instance arithmeticFactorRatioLabeledInitialMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (f b) := by
  let _ := hn
  rw [arithmeticFactorRatioLabeledInitialMap_normalized]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

omit [IsDomain R] in
/-- The arithmetic initial image is exactly D(y - 1), without reduction of the base ring. -/
theorem arithmeticInitialFactorRatioChart_image :
    Set.range N = (PrimeSpectrum.basicOpen (rightCoordinate τ - 1) :
      Set (PrimeSpectrum (ChartRing τ))) :=
  polynomialFactorRatioChart_range ..

/-- Both initial images use the original polygon indices and exact branch orientation. -/
theorem arithmeticFactorRatioLabeledInitialMap_range (b : Bool) :
    Set.range (f b) = (O b ≫ c (initialPolygonIndex k b)) ''
      (PrimeSpectrum.basicOpen (rightCoordinate τ - 1) : Set (PrimeSpectrum (ChartRing τ))) := by
  rw [arithmeticFactorRatioLabeledInitialMap_normalized]
  change Set.range ((O b ≫ c (initialPolygonIndex k b)) ∘ N) = _
  rw [Set.range_comp, arithmeticInitialFactorRatioChart_image data H m]

/-- The full oriented infinity edge fills the complement of each original initial label. -/
theorem arithmeticFactorRatioLabeledInitialMap_edge_cover (b : Bool)
    (x : PolygonSmoothing.chart Q τ) :
    (O b ≫ c (initialPolygonIndex k b)) x ∈ Set.range (f b) ∨
      (O b ≫ c (initialPolygonIndex k b)) x ∈
        Set.range (rightBranchOpen Q τ ≫ O b ≫ c (initialPolygonIndex k b)) := by
  have hx : x ∈ Set.range N ∨ x ∈ Set.range (rightBranchOpen Q τ) :=
    polynomialFactorRatioChart_right_cover ..
  rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · left
    refine ⟨z, ?_⟩
    rw [arithmeticFactorRatioLabeledInitialMap_normalized]
    rfl
  · exact Or.inr ⟨z, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
