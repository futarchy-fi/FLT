/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroLast
public import FLT.Mazur.WeierstrassDividedResidualLiftPunctures

/-!
# Both punctures of the accumulated last-node factor

The direct initial edge and the closing edge keep the same four full factors.
Their algebra substitutions are composed in contravariant order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "O" => twistedRetainedOrientation data H m
local notation "A₁" => arithmeticResidualLiftRetainedPuncture hπ data H m j hj u hu
local notation "A₂" => fun b a ↦ twoBranchCorrectionPunctureFactor R π m τ
  (arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu b) a
local notation "A₃" => fun b a ↦ twoBranchCorrectionPunctureFactor R π m τ
  (arithmeticThirdLastIntegralField hπ data H j hj u hu b) a
local notation "A₄" => fun b a ↦ twoBranchCorrectionPunctureFactor R π m τ
  (arithmeticFourthLastIntegralField hπ data H j hj u hu b) a

/-- The second oriented last factor retains the direct substitution on either puncture. -/
@[reassoc] theorem arithmeticZeroSecondJointOrientedIso_puncture (b a : Bool) :
    (punctureOpen τ a ≫ (O b).hom) ≫
        (arithmeticSecondJointOrientedIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (A₂ b a)).hom ≫ punctureOpen τ a ≫ (O b).hom := by
  rw [Category.assoc, arithmeticSecondJointOrientedIso_hom,
    ← Category.assoc, arithmeticSecondJointRetainedIso_puncture, Category.assoc]

/-- The third oriented last factor retains the direct substitution on either puncture. -/
@[reassoc] theorem arithmeticZeroThirdLastOrientedIso_puncture (b a : Bool) :
    (punctureOpen τ a ≫ (O b).hom) ≫
        (arithmeticThirdLastOrientedIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (A₃ b a)).hom ≫ punctureOpen τ a ≫ (O b).hom := by
  rw [Category.assoc, arithmeticThirdLastOrientedIso_hom,
    ← Category.assoc, arithmeticThirdLastIso_puncture, Category.assoc]

/-- The fourth oriented last factor retains the direct substitution on either puncture. -/
@[reassoc] theorem arithmeticZeroFourthLastOrientedIso_puncture (b a : Bool) :
    (punctureOpen τ a ≫ (O b).hom) ≫
        (arithmeticFourthLastOrientedIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (A₄ b a)).hom ≫ punctureOpen τ a ≫ (O b).hom := by
  rw [Category.assoc, arithmeticFourthLastOrientedIso_hom,
    ← Category.assoc, arithmeticFourthLastIso_puncture, Category.assoc]

/-- The exact full substitution induced by the accumulated four-round last factor. -/
def arithmeticFourthAccumulatedLastPuncture (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (((A₄ b a).trans (A₃ b a)).trans (A₂ b a)).trans (A₁ b a)

/-- Both direct punctures are the spectra of their entire accumulated algebra substitutions. -/
@[reassoc] theorem arithmeticFourthAccumulatedLastIso_puncture (b a : Bool) :
    (punctureOpen τ a ≫ (O b).hom) ≫
        (arithmeticFourthAccumulatedLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso
        (arithmeticFourthAccumulatedLastPuncture hπ data H m j hj u hu b a)).hom ≫
          punctureOpen τ a ≫ (O b).hom := by
  simp only [arithmeticFourthAccumulatedLastIso, arithmeticFourthAccumulatedLastPuncture,
    Iso.trans_hom, punctureSpecIso_trans, Category.assoc]
  rw [arithmeticResidualLiftOrientedIso_puncture_assoc,
    arithmeticZeroSecondJointOrientedIso_puncture_assoc,
    arithmeticZeroThirdLastOrientedIso_puncture_assoc,
    ← Category.assoc (punctureOpen τ a), arithmeticZeroFourthLastOrientedIso_puncture]

end FLT.Mazur.WeierstrassDividedDepth
