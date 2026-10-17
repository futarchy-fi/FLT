/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthNodeRestriction

/-!
# Original coefficient squares for the fifth depth-two geometric factors

Each restriction is the actual coefficient map on the stated old or new
smoothing. The predecessor uses normalized coordinates; the last node retains its orientation.
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
local notation "L" => fun k ↦ arithmeticFifthShallowLastIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthShallowLastOrientedIso hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticFifthShallowPrecedingIso hπ data H k j hj u hu
local notation "s" => arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu

/-- The whole last-node correction respects the original normalized quotient. -/
@[reassoc] theorem arithmeticFifthShallowLastIso_restriction (b : Bool) :
    N ≫ (L (m + 1) b).hom = (L m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthShallowLastFactor_restriction hπ data H j hj u hu m b)
    _ _ (arithmeticFifthShallowLastSmoothing_pair hπ data H j hj u hu (m + 1) b)
    (arithmeticFifthShallowLastSmoothing_pair hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- The last label retains its orientation and the full coefficient square. -/
@[reassoc] theorem arithmeticFifthShallowLastOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticFifthShallowLastOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N, arithmeticFifthShallowLastIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

/-- The new predecessor's explicit coefficient restriction. -/
def arithmeticFifthShallowPrecedingRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthShallowPrecedingSmoothing_restriction hπ data H j hj u hu m b)))

/-- Both old and new predecessor smoothings occur in the actual factor square. -/
@[reassoc] theorem arithmeticFifthShallowPrecedingIso_restriction (b : Bool) :
    arithmeticFourthPrecedingRestriction hπ data H j hj u hu m b ≫ (P (m + 1) b).hom =
      (P m b).hom ≫ arithmeticFifthShallowPrecedingRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthShallowPrecedingFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
