/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialGeometry
public import FLT.Mazur.WeierstrassDividedFifthInitialRestriction
public import FLT.Mazur.WeierstrassDividedFourthInitialNodeRestriction

/-!
# Coefficient squares for the fifth depth-one geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The initial node and its neighbor already have normalized coordinates.
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
local notation "P" => fun k ↦ arithmeticFifthInitialNeighborIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticFifthInitialNodeIso hπ data H k j hj u hu
local notation "s" => arithmeticFifthInitialNeighborSmoothing hπ data H j hj u hu
local notation "t" => arithmeticFifthInitialSmoothing hπ data H j hj u hu

/-- The new earlier neighbor's explicit coefficient restriction. -/
def arithmeticFifthInitialNeighborRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticFifthInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthInitialSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new earlier neighbor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFifthInitialNeighborIso_restriction (b : Bool) :
    arithmeticFourthInitialNeighborRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFifthInitialNeighborRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthInitialNeighborFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its original smoothing. -/
@[reassoc] theorem arithmeticFifthInitialNodeIso_restriction (b : Bool) :
    arithmeticFourthInitialNodeRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticFifthInitialNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthInitialFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
