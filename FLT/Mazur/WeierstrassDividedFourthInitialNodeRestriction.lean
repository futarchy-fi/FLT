/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialGeometry
public import FLT.Mazur.WeierstrassDividedFourthInitialRestriction
public import FLT.Mazur.WeierstrassDividedThirdNodeRestriction

/-!
# Coefficient squares for the fourth depth-one geometric factors

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
local notation "P" => fun k ↦ arithmeticFourthInitialNeighborIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticFourthInitialNodeIso hπ data H k j hj u hu
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu
local notation "t" => arithmeticFourthInitialSmoothing hπ data H j hj u hu

/-- The new predecessor's explicit coefficient restriction. -/
def arithmeticFourthInitialNeighborRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b)))

/-- The initial node's new scalar drift is retained by its explicit quotient. -/
def arithmeticFourthInitialNodeRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new predecessor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFourthInitialNeighborIso_restriction (b : Bool) :
    arithmeticThirdPrecedingRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFourthInitialNeighborRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthInitialNeighborFactor_restriction hπ data H j hj u hu m b)

/-- The initial full factor keeps the coefficient square on its changed third smoothing. -/
@[reassoc] theorem arithmeticFourthInitialNodeIso_restriction (b : Bool) :
    arithmeticThirdEarlierRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticFourthInitialNodeRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthInitialFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
