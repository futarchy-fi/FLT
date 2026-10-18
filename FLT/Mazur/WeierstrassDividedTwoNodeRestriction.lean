/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowNodeRestriction
public import FLT.Mazur.WeierstrassDividedTwoFactorRestriction
public import FLT.Mazur.WeierstrassDividedTwoFiniteGeometry

/-!
# Coefficient squares for the finite depth-two geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The initial node and the three retained nodes have normalized coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (k m : ℕ)
local notation "P" => fun l ↦ arithmeticTwoFiniteRetainedIso hπ data H k l hj u hu
local notation "E" => fun l ↦ arithmeticTwoFiniteInitialNodeIso hπ data H k l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoFiniteState hπ data H hj u hu k)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticTwoFiniteState hπ data H hj u hu k)

/-- The exact retained seed coefficient map, before further corrections. -/
def arithmeticTwoSeedRetainedRestriction (i : Fin 3) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m)
        ((arithmeticTwoSeedState hπ data H hj u hu).retained m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1))
        ((arithmeticTwoSeedState hπ data H hj u hu).retained (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoSeedState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticTwoFiniteRetainedRestriction (i : Fin 3) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoFiniteState_compatible hπ data H hj u hu k).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticTwoFiniteInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoFiniteState_compatible hπ data H hj u hu k).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticTwoFiniteRetainedIso_restriction (i : Fin 3) (b : Bool) :
    arithmeticTwoSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticTwoFiniteRetainedRestriction hπ data H hj u hu k m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoFiniteRetainedFactor_restriction hπ data H hj u hu k m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticTwoFiniteInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthShallowNodeRestriction hπ data H 2 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticTwoFiniteInitialNodeRestriction hπ data H hj u hu k m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoFiniteInitialFactor_restriction hπ data H hj u hu k m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticTwoFiniteState hπ data H hj u hu k)
local notation "F" => fun l ↦ arithmeticTwoFiniteTerminalIso hπ data H k l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticTwoFiniteTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoFiniteState_compatible hπ data H hj u hu k).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticTwoFiniteTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 2 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticTwoFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoFiniteTerminalFactor_restriction hπ data H hj u hu k m)).symm

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Coefficient squares for the diagonal depth-two geometric factors

The correction count varies with arithmetic order. Each geometric square
uses the coefficient map on the actual accumulated diagonal smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "P" => fun l ↦ arithmeticTwoFiniteRetainedIso hπ data H l l hj u hu
local notation "E" => fun l ↦ arithmeticTwoFiniteInitialNodeIso hπ data H l l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoDiagonalState hπ data H hj u hu)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticTwoDiagonalState hπ data H hj u hu)

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticTwoDiagonalRetainedRestriction (i : Fin 3) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoDiagonalState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticTwoDiagonalInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoDiagonalState_compatible hπ data H hj u hu).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticTwoDiagonalRetainedIso_restriction (i : Fin 3) (b : Bool) :
    arithmeticTwoSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticTwoDiagonalRetainedRestriction hπ data H hj u hu m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoDiagonalRetainedFactor_restriction hπ data H hj u hu m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticTwoDiagonalInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthShallowNodeRestriction hπ data H 2 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticTwoDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoDiagonalInitialFactor_restriction hπ data H hj u hu m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticTwoDiagonalState hπ data H hj u hu)
local notation "F" => fun l ↦ arithmeticTwoFiniteTerminalIso hπ data H l l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticTwoDiagonalTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticTwoDiagonalState_compatible hπ data H hj u hu).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticTwoDiagonalTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 2 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticTwoDiagonalTerminalRestriction hπ data H hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticTwoDiagonalTerminalFactor_restriction hπ data H hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
