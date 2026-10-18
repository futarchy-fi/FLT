/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodeRestriction
public import FLT.Mazur.WeierstrassDividedThreeFactorRestriction
public import FLT.Mazur.WeierstrassDividedThreeFiniteGeometry

/-!
# Coefficient squares for the finite depth-three geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The initial node and the four retained nodes have normalized coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (k m : ℕ)
local notation "P" => fun l ↦ arithmeticThreeFiniteRetainedIso hπ data H k l hj u hu
local notation "E" => fun l ↦ arithmeticThreeFiniteInitialNodeIso hπ data H k l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticThreeFiniteState hπ data H hj u hu k)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticThreeFiniteState hπ data H hj u hu k)

/-- The exact retained seed coefficient map, before further corrections. -/
def arithmeticThreeSeedRetainedRestriction (i : Fin 4) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m)
        ((arithmeticThreeSeedState hπ data H hj u hu).retained m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1))
        ((arithmeticThreeSeedState hπ data H hj u hu).retained (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeSeedState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticThreeFiniteRetainedRestriction (i : Fin 4) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeFiniteState_compatible hπ data H hj u hu k).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticThreeFiniteInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeFiniteState_compatible hπ data H hj u hu k).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticThreeFiniteRetainedIso_restriction (i : Fin 4) (b : Bool) :
    arithmeticThreeSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticThreeFiniteRetainedRestriction hπ data H hj u hu k m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeFiniteRetainedFactor_restriction hπ data H hj u hu k m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticThreeFiniteInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthFartherNodeRestriction hπ data H 3 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticThreeFiniteInitialNodeRestriction hπ data H hj u hu k m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeFiniteInitialFactor_restriction hπ data H hj u hu k m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 3 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticThreeFiniteState hπ data H hj u hu k)
local notation "F" => fun l ↦ arithmeticThreeFiniteTerminalIso hπ data H k l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticThreeFiniteTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeFiniteState_compatible hπ data H hj u hu k).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticThreeFiniteTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 3 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticThreeFiniteTerminalRestriction hπ data H hj u hu k m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeFiniteTerminalFactor_restriction hπ data H hj u hu k m)).symm

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Coefficient squares for the diagonal depth-three geometric factors

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
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "P" => fun l ↦ arithmeticThreeFiniteRetainedIso hπ data H l l hj u hu
local notation "E" => fun l ↦ arithmeticThreeFiniteInitialNodeIso hπ data H l l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticThreeDiagonalState hπ data H hj u hu)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticThreeDiagonalState hπ data H hj u hu)

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticThreeDiagonalRetainedRestriction (i : Fin 4) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeDiagonalState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticThreeDiagonalInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeDiagonalState_compatible hπ data H hj u hu).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticThreeDiagonalRetainedIso_restriction (i : Fin 4) (b : Bool) :
    arithmeticThreeSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticThreeDiagonalRetainedRestriction hπ data H hj u hu m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeDiagonalRetainedFactor_restriction hπ data H hj u hu m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticThreeDiagonalInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthFartherNodeRestriction hπ data H 3 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticThreeDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeDiagonalInitialFactor_restriction hπ data H hj u hu m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 3 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticThreeDiagonalState hπ data H hj u hu)
local notation "F" => fun l ↦ arithmeticThreeFiniteTerminalIso hπ data H l l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticThreeDiagonalTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticThreeDiagonalState_compatible hπ data H hj u hu).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticThreeDiagonalTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 3 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticThreeDiagonalTerminalRestriction hπ data H hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThreeDiagonalTerminalFactor_restriction hπ data H hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
