/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthGeometry
public import FLT.Mazur.WeierstrassDividedThirdNodeRestriction

/-!
# Original coefficient squares for the fourth geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. Both the predecessor and the earlier node already have normalized coordinates.
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
local notation "N" => closingNormalizedRestriction data H m
local notation "L" => fun k ↦ arithmeticFourthLastIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthLastOrientedIso hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticFourthPrecedingIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticFourthEarlierIso hπ data H k j hj u hu
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu
local notation "t" => arithmeticFourthEarlierSmoothing hπ data H j hj u hu

/-- The whole last-node correction respects the original normalized quotient. -/
@[reassoc] theorem arithmeticFourthLastIso_restriction (b : Bool) :
    N ≫ (L (m + 1) b).hom = (L m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthLastFactor_restriction hπ data H j hj u hu m b)
    _ _ (arithmeticFourthLastSmoothing_pair hπ data H j hj u hu (m + 1) b)
    (arithmeticFourthLastSmoothing_pair hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- The last label retains its orientation and the full coefficient square. -/
@[reassoc] theorem arithmeticFourthLastOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticFourthLastOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N, arithmeticFourthLastIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

/-- The new predecessor's explicit coefficient restriction. -/
def arithmeticFourthPrecedingRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthPrecedingSmoothing_restriction hπ data H j hj u hu m b)))

/-- The earlier node's new scalar drift is retained by its explicit quotient. -/
def arithmeticFourthEarlierRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFourthEarlierSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new predecessor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFourthPrecedingIso_restriction (b : Bool) :
    arithmeticThirdPrecedingRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFourthPrecedingRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthPrecedingFactor_restriction hπ data H j hj u hu m b)

/-- The earlier full factor keeps the coefficient square on its changed third smoothing. -/
@[reassoc] theorem arithmeticFourthEarlierIso_restriction (b : Bool) :
    arithmeticThirdEarlierRestriction hπ data H j hj u hu m b ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticFourthEarlierRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFourthEarlierFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
