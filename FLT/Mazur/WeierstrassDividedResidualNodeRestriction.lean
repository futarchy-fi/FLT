/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingFactorRestriction
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasSystem

/-!
# Explicit coefficient restriction of the first installed retained corrections

The full node correction and its original branch orientation both preserve
the actual normalized coefficient map. Thus transport in the residual atlas
does not introduce a different restriction on any retained label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "N" => closingNormalizedRestriction data H m
local notation "O" => fun k ↦ twistedRetainedOrientation data H k
local notation "A" => fun k ↦ arithmeticResidualLiftRetainedIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticResidualLiftOrientedIso hπ data H k j hj u hu

omit [IsDomain R] in
/-- The original branch orientation commutes with the full coefficient quotient. -/
@[reassoc] theorem twistedRetainedOrientation_restriction (b : Bool) :
    N ≫ (O (m + 1) b).hom = (O m b).hom ≫ N := by
  cases b
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (branchSwapIso_ringMap (restriction R π m).toRingHom _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).symm

omit [IsDomain R] in
/-- Removing the original orientation also preserves the complete coefficient quotient. -/
@[reassoc] theorem twistedRetainedOrientation_inv_restriction (b : Bool) :
    N ≫ (O (m + 1) b).inv = (O m b).inv ≫ N := by
  apply (cancel_epi (O m b).hom).mp
  rw [← Category.assoc, ← twistedRetainedOrientation_restriction data H m b,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The full first retained correction preserves both original quotient coordinates. -/
@[reassoc] theorem arithmeticResidualLiftRetainedIso_restriction (b : Bool) :
    N ≫ (A (m + 1) b).hom = (A m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticResidualRetainedLift_restriction hπ data H j hj u hu m b) _ _
    (arithmeticResidualRetainedLift_smoothing hπ data H j hj u hu (m + 1) b)
    (arithmeticResidualRetainedLift_smoothing hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- Conjugation by the actual labeled orientation retains the explicit coefficient square. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticResidualLiftOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N,
    arithmeticResidualLiftRetainedIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

/-- Every retained restriction in the first residual atlas is its actual coefficient map. -/
theorem arithmeticResidualLiftAtlasRestriction_retained
    (a : Fin (j + 1)) (b : Bool) :
    arithmeticResidualLiftAtlasRestriction hπ data H j hj u hu m (.retained a b) = N := by
  unfold arithmeticResidualLiftAtlasRestriction
  change (arithmeticResidualLiftAtlasCorrection hπ data H m j hj u hu (.retained a b)).inv ≫
    N ≫ (arithmeticResidualLiftAtlasCorrection
      hπ data H (m + 1) j hj u hu (.retained a b)).hom = N
  simp only [arithmeticResidualLiftAtlasCorrection]
  split_ifs with ha
  · rw [arithmeticResidualLiftOrientedIso_restriction, Iso.inv_hom_id_assoc]
  · exact (Category.id_comp _).trans (Category.comp_id _)

end FLT.Mazur.WeierstrassDividedDepth
