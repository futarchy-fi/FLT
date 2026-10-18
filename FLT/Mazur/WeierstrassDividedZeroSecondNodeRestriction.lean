/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondGeometry
public import FLT.Mazur.WeierstrassDividedZeroSecondRestriction
public import FLT.Mazur.WeierstrassDividedZeroFirstNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry

/-!
# Coefficient squares for the second depth-zero geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The initial node and the unique last node have normalized coordinates.
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
local notation "P" => fun k ↦ arithmeticZeroSecondLastIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticZeroSecondInitialNodeIso hπ data H k j hj u hu
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H j hj u hu
local notation "t" => arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu

/-- The new last node's explicit coefficient restriction. -/
def arithmeticZeroSecondLastRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticZeroSecondInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroSecondInitialSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new last node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticZeroSecondLastIso_restriction (b : Bool) :
    arithmeticZeroFirstLastRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticZeroSecondLastRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroSecondLastFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its actual first smoothing. -/
@[reassoc] theorem arithmeticZeroSecondInitialNodeIso_restriction (b : Bool) :
    arithmeticZeroFirstInitialNodeRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticZeroSecondInitialNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroSecondInitialFactor_restriction hπ data H j hj u hu m b)

local notation "t₀" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu
local notation "T" => arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu
local notation "F" => fun k ↦ arithmeticZeroSecondTerminalIso hπ data H k j hj u hu

/-- The terminal coefficient map keeps its exact second smoothing. -/
def arithmeticZeroSecondTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroSecondTerminalSmoothing_restriction hπ data H j hj u hu m)))

/-- The geometric inverse has the full square on the actual full first terminal. -/
@[reassoc] theorem arithmeticZeroSecondTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticZeroSecondTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroSecondTerminalFactor_restriction hπ data H j hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
