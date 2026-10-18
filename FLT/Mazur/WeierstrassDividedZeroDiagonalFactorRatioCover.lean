/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatio

/-!
# Exact images and full initial-node coverage after factor-ratio transport

The deleted tangent divisor is transported through the entire node isomorphism.
The original full infinity-side puncture covers its complement at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalInitialOpenIso arithmeticZeroDiagonalInitialTotalNodeIso
/-- Full open images transport through source and target isomorphisms. -/
theorem factorRatioIsoTransport_range {A A' X X' : Scheme}
    (e : A ≅ A') (t : X ≅ X') (f : A ⟶ X) :
    Set.range (e.inv ≫ f ≫ t.hom) = t.hom '' Set.range f := by
  change Set.range (t.hom ∘ f ∘ e.inv) = _
  have he : Function.Surjective e.inv := e.inv.homeomorph.surjective
  rw [Set.range_comp, Set.range_comp, he.range_eq, Set.image_univ]

/-- A full two-open cover survives both source and target transport and an inclusion. -/
theorem factorRatioIsoTransport_cover {A A' B X X' Y : Scheme}
    (e : A ≅ A') (t : X ≅ X') (f : A ⟶ X) (g : B ⟶ X) (c : X' ⟶ Y)
    (h : ∀ x : X, x ∈ Set.range f ∨ x ∈ Set.range g) (x : X') :
    c x ∈ Set.range (e.inv ≫ f ≫ t.hom ≫ c) ∨
      c x ∈ Set.range (g ≫ t.hom ≫ c) := by
  obtain ⟨z, rfl⟩ := t.hom.homeomorph.surjective x
  rcases h z with ⟨w, hw⟩ | ⟨w, hw⟩
  · left
    refine ⟨e.hom w, ?_⟩
    have hf := congrArg (fun k ↦ k w) (e.hom_inv_id_assoc (f ≫ t.hom ≫ c))
    exact hf.trans (congrArg (fun z ↦ c (t.hom z)) hw)
  · right
    exact ⟨w, congrArg (fun z ↦ c (t.hom z)) hw⟩

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m

/-- The exact full open image transports the original deleted tangent divisor. -/
theorem arithmeticZeroDiagonalInitialFactorRatio_range (b : Bool) :
    Set.range (F b) = (T b).hom ''
      (PrimeSpectrum.basicOpen (rightCoordinate τ - 1) : Set (PrimeSpectrum (ChartRing τ))) := by
  rw [arithmeticZeroDiagonalInitialFactorRatio, factorRatioIsoTransport_range,
    arithmeticInitialFactorRatioChart_image data H m]

/-- The whole original infinity-side puncture is transported through all initial node factors. -/
def arithmeticZeroDiagonalInitialInfinityBoundary (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  rightBranchOpen Q τ ≫ (T b).hom ≫ C b

local notation "B" => arithmeticZeroDiagonalInitialInfinityBoundary hπ data H m hj u hu

instance arithmeticZeroDiagonalInitialInfinityBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (B b) := by
  unfold arithmeticZeroDiagonalInitialInfinityBoundary
  infer_instance

/-- The actual initial node is covered by its full factor-ratio open and infinity-side edge. -/
theorem arithmeticZeroDiagonalInitialFactorRatio_cover (b : Bool)
    (x : PolygonSmoothing.chart Q (s b)) :
    C b x ∈ Set.range (f b) ∨ C b x ∈ Set.range (B b) := by
  simpa only [arithmeticZeroDiagonalFactorRatioInitialMap,
    arithmeticZeroDiagonalInitialFactorRatio, arithmeticZeroDiagonalInitialInfinityBoundary,
    Category.assoc] using
    factorRatioIsoTransport_cover (E b) (T b) N (rightBranchOpen Q τ) (C b)
      (revisedInitialNode_right_cover τ N (arithmeticInitialFactorRatioChart_image data H m)) x

end FLT.Mazur.WeierstrassDividedDepth
