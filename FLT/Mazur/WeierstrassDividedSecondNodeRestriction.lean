/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdJointRestriction

/-!
# Exact quotient squares for the simultaneous second node corrections

The last retained node uses its unchanged smoothing, while its predecessor
and terminal retain their actual accumulated scalar drifts.
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
local notation "A" => fun k ↦ arithmeticSecondJointRetainedIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticSecondJointOrientedIso hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticSecondPrecedingOrientedIso hπ data H k j hj u hu
local notation "s" => fun k ↦ arithmeticSecondPrecedingSmoothing hπ data H k j hj u hu

/-- The normalized shared second correction preserves both full quotient coordinates. -/
@[reassoc] theorem arithmeticSecondJointRetainedIso_restriction (b : Bool) :
    N ≫ (A (m + 1) b).hom = (A m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (twoBranchCorrectionNodeFactor_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _)
    _ _ (arithmeticSecondJointRetainedSmoothing_pair hπ data H j hj u hu (m + 1) b)
    (arithmeticSecondJointRetainedSmoothing_pair hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- The actual oriented shared correction preserves the original coefficient quotient. -/
@[reassoc] theorem arithmeticSecondJointOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticSecondJointOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N,
    arithmeticSecondJointRetainedIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

/-- The predecessor's explicit quotient retains its exact second smoothing. -/
def arithmeticSecondPrecedingRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b)))

local notation "ρ" => arithmeticSecondPrecedingRestriction hπ data H j hj u hu m

/-- The predecessor's entire normalized correction keeps its original quotient square. -/
@[reassoc] theorem arithmeticSecondPrecedingIso_restriction (b : Bool) :
    N ≫ (arithmeticSecondPrecedingIso hπ data H (m + 1) j hj u hu b).hom =
      (arithmeticSecondPrecedingIso hπ data H m j hj u hu b).hom ≫ ρ b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (correctionNodeFactor_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _)

/-- Removing the predecessor orientation keeps the coefficient square on its changed smoothing. -/
@[reassoc] theorem arithmeticSecondPrecedingOrientedIso_restriction (b : Bool) :
    N ≫ (P (m + 1) b).hom = (P m b).hom ≫ ρ b := by
  simp only [arithmeticSecondPrecedingOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, arithmeticSecondPrecedingIso_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
