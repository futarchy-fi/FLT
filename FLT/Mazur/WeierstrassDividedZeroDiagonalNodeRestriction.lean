/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteGeometry
public import FLT.Mazur.WeierstrassDividedZeroDiagonalRestriction
public import FLT.Mazur.WeierstrassDividedZeroFifthNodeRestriction

/-!
# Coefficient squares for the diagonal depth-zero geometric factors

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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "P" => fun l ↦ arithmeticZeroFiniteLastIso hπ data H l l j hj u hu
local notation "E" => fun l ↦ arithmeticZeroFiniteInitialNodeIso hπ data H l l j hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last
  (arithmeticZeroDiagonalState hπ data H j hj u hu)
local notation "t" => PolygonArithmeticSimultaneous.State.initial
  (arithmeticZeroDiagonalState hπ data H j hj u hu)

/-- The new last node's explicit coefficient restriction. -/
def arithmeticZeroDiagonalLastRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticZeroDiagonalState_compatible hπ data H j hj u hu).2.1 m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticZeroDiagonalInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticZeroDiagonalState_compatible hπ data H j hj u hu).1 m b)))

/-- Both old and new last node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticZeroDiagonalLastIso_restriction (b : Bool) :
    arithmeticZeroFifthLastRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticZeroDiagonalLastRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroDiagonalLastFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialNodeIso_restriction (b : Bool) :
    arithmeticZeroFifthInitialNodeRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticZeroDiagonalInitialNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroDiagonalInitialFactor_restriction hπ data H j hj u hu m b)

local notation "t₀" => arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu
local notation "T" => PolygonArithmeticSimultaneous.State.terminal
  (arithmeticZeroDiagonalState hπ data H j hj u hu)
local notation "F" => fun l ↦ arithmeticZeroFiniteTerminalIso hπ data H l l j hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticZeroDiagonalTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticZeroDiagonalState_compatible hπ data H j hj u hu).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticZeroDiagonalTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticZeroFifthTerminalSmoothing_restriction hπ data H j hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticZeroDiagonalTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroDiagonalTerminalFactor_restriction hπ data H j hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
