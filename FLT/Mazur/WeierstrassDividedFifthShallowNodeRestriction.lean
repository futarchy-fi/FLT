/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowGeometry
public import FLT.Mazur.WeierstrassDividedFifthShallowRestriction
public import FLT.Mazur.WeierstrassDividedFourthShallowNodeRestriction

/-!
# Coefficient squares for the fifth depth-two geometric factors

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
local notation "P" => fun k ↦ arithmeticFifthShallowNeighborIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticFifthShallowNodeIso hπ data H k j hj u hu
local notation "s" => arithmeticFifthShallowNeighborSmoothing hπ data H j hj u hu
local notation "t" => arithmeticFifthShallowSmoothing hπ data H j hj u hu

/-- The new earlier neighbor's explicit coefficient restriction. -/
def arithmeticFifthShallowNeighborRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticFifthShallowNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthShallowSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new earlier neighbor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFifthShallowNeighborIso_restriction (b : Bool) :
    arithmeticFourthShallowNeighborRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFifthShallowNeighborRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthShallowNeighborFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its original smoothing. -/
@[reassoc] theorem arithmeticFifthShallowNodeIso_restriction (b : Bool) :
    arithmeticFourthShallowNodeRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticFifthShallowNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthShallowFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
