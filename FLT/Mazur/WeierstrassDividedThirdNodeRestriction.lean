/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdGeometry

/-!
# Original coefficient squares for the third geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The predecessor is already normalized by the second correction.
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
local notation "L" => fun k ↦ arithmeticThirdLastIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticThirdLastOrientedIso hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticThirdPrecedingIso hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticThirdEarlierIso hπ data H k j hj u hu
local notation "A" => fun k ↦ arithmeticThirdEarlierOrientedIso hπ data H k j hj u hu
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu
local notation "t" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu

/-- The whole last-node correction respects the original normalized quotient. -/
@[reassoc] theorem arithmeticThirdLastIso_restriction (b : Bool) :
    N ≫ (L (m + 1) b).hom = (L m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThirdLastFactor_restriction hπ data H j hj u hu m b)
    _ _ (arithmeticThirdLastSmoothing_pair hπ data H j hj u hu (m + 1) b)
    (arithmeticThirdLastSmoothing_pair hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- The last label retains its orientation and the full coefficient square. -/
@[reassoc] theorem arithmeticThirdLastOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticThirdLastOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N, arithmeticThirdLastIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

/-- The new predecessor's explicit coefficient restriction. -/
def arithmeticThirdPrecedingRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b)))

/-- The earlier node's new scalar drift is retained by its explicit quotient. -/
def arithmeticThirdEarlierRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new predecessor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticThirdPrecedingIso_restriction (b : Bool) :
    arithmeticSecondPrecedingRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticThirdPrecedingRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThirdPrecedingFactor_restriction hπ data H j hj u hu m b)

/-- The earlier full factor keeps the coefficient square before orientation. -/
@[reassoc] theorem arithmeticThirdEarlierIso_restriction (b : Bool) :
    N ≫ (E (m + 1) b).hom =
      (E m b).hom ≫ arithmeticThirdEarlierRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticThirdEarlierFactor_restriction hπ data H j hj u hu m b)

/-- Removing the earlier label's orientation respects the same full quotient square. -/
@[reassoc] theorem arithmeticThirdEarlierOrientedIso_restriction (b : Bool) :
    N ≫ (A (m + 1) b).hom =
      (A m b).hom ≫ arithmeticThirdEarlierRestriction hπ data H j hj u hu m b := by
  simp only [arithmeticThirdEarlierOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, arithmeticThirdEarlierIso_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
