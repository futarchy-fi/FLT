/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteGeometry
public import FLT.Mazur.WeierstrassDividedOneDiagonalRestriction
public import FLT.Mazur.WeierstrassDividedOneFiniteNodeRestriction

/-!
# Coefficient squares for the diagonal depth-one geometric factors

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
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "P" => fun l ↦ arithmeticOneFiniteRetainedIso hπ data H l l hj u hu
local notation "E" => fun l ↦ arithmeticOneFiniteInitialNodeIso hπ data H l l hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticOneDiagonalState hπ data H hj u hu)
local notation "t" => PolygonArithmeticRetainedChain.State.initial
  (arithmeticOneDiagonalState hπ data H hj u hu)

/-- The new retained node's explicit coefficient restriction. -/
def arithmeticOneDiagonalRetainedRestriction (i : Fin 2) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m i b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) i b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneDiagonalState_compatible hπ data H hj u hu).2.1 m i b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticOneDiagonalInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneDiagonalState_compatible hπ data H hj u hu).1 m b)))

/-- Both old and new retained node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticOneDiagonalRetainedIso_restriction (i : Fin 2) (b : Bool) :
    arithmeticOneSeedRetainedRestriction hπ data H hj u hu m i b ≫ (P (m + 1) i b).hom =
      (P m i b).hom ≫ arithmeticOneDiagonalRetainedRestriction hπ data H hj u hu m i b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneDiagonalRetainedFactor_restriction hπ data H hj u hu m i b)

/-- The initial full factor keeps the coefficient square on its actual fifth smoothing. -/
@[reassoc] theorem arithmeticOneDiagonalInitialNodeIso_restriction (b : Bool) :
    arithmeticFifthInitialNodeRestriction hπ data H 1 hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticOneDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneDiagonalInitialFactor_restriction hπ data H hj u hu m b)

local notation "t₀" => arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu
local notation "T" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticOneDiagonalState hπ data H hj u hu)
local notation "F" => fun l ↦ arithmeticOneFiniteTerminalIso hπ data H l l hj u hu

/-- The terminal coefficient map keeps its exact finite smoothing. -/
def arithmeticOneDiagonalTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    ((arithmeticOneDiagonalState_compatible hπ data H hj u hu).2.2.1 m)))

/-- The geometric inverse has the full square on the actual full fifth terminal. -/
@[reassoc] theorem arithmeticOneDiagonalTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 1 hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticOneDiagonalTerminalRestriction hπ data H hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticOneDiagonalTerminalFactor_restriction hπ data H hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
