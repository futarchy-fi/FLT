/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthGeometry
public import FLT.Mazur.WeierstrassDividedZeroFifthRestriction
public import FLT.Mazur.WeierstrassDividedZeroFourthNodeRestriction

/-!
# Coefficient squares for the fifth depth-zero geometric factors

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
local notation "P" => fun k ↦ arithmeticZeroFifthLastIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticZeroFifthInitialNodeIso hπ data H k j hj u hu
local notation "s" => arithmeticZeroFifthLastSmoothing hπ data H j hj u hu
local notation "t" => arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu

/-- The new last node's explicit coefficient restriction. -/
def arithmeticZeroFifthLastRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroFifthLastSmoothing_restriction hπ data H j hj u hu m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticZeroFifthInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroFifthInitialSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new last node smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticZeroFifthLastIso_restriction (b : Bool) :
    arithmeticZeroFourthLastRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticZeroFifthLastRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroFifthLastFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its actual fourth smoothing. -/
@[reassoc] theorem arithmeticZeroFifthInitialNodeIso_restriction (b : Bool) :
    arithmeticZeroFourthInitialNodeRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticZeroFifthInitialNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroFifthInitialFactor_restriction hπ data H j hj u hu m b)

local notation "t₀" => arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu
local notation "T" => arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu
local notation "F" => fun k ↦ arithmeticZeroFifthTerminalIso hπ data H k j hj u hu

/-- The terminal coefficient map keeps its exact fifth smoothing. -/
def arithmeticZeroFifthTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticZeroFifthTerminalSmoothing_restriction hπ data H j hj u hu m)))

/-- The geometric inverse has the full square on the actual full fourth terminal. -/
@[reassoc] theorem arithmeticZeroFifthTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t₀ (m + 1)) (t₀ m)
        (arithmeticZeroFourthTerminalSmoothing_restriction hπ data H j hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticZeroFifthTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticZeroFifthTerminalFactor_restriction hπ data H j hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
